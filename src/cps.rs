//! CPS evaluator with first-class continuations.
//!
//! Replaces the tree-walking evaluator with an explicit continuation-passing
//! machine. Continuations are rib chains on the heap, so call/cc just
//! captures the current continuation pointer.
//!
//! Based on the defunctionalized CPS pattern from the Psi-Lisp
//! metacircular evaluator (psi_metacircular.lisp).
//!
//! State machine: the evaluator is a loop over three states:
//!   Eval(expr, env, cont)       — evaluate an expression
//!   ApplyCont(val, cont)        — deliver a value to a continuation
//!   ApplyProc(proc, args, cont) — apply a procedure to arguments

use crate::heap::Heap;
use crate::symbol::SymbolTable;
use crate::val::Val;
use crate::table;

// ── Continuation frame types ─────────────────────────────────────
// Stored as fixnum tags in the car of continuation ribs.

const K_DONE: i64 = 0;
const K_IF: i64 = 1;        // (tag, consequent, alternate, env)
const K_SET: i64 = 2;       // (tag, var, env)
const K_DEFINE: i64 = 3;    // (tag, var)
const K_BEGIN: i64 = 4;     // (tag, remaining_exprs, env)
const K_EVFN: i64 = 5;      // (tag, arg_exprs, env) — operator done, eval args
const K_EVARG: i64 = 6;     // (tag, remaining, done_rev, proc, env) — one arg done
const K_AND: i64 = 7;       // (tag, remaining, env)
const K_OR: i64 = 8;        // (tag, remaining, env)

/// The CPS evaluator.
pub struct CpsEval {
    pub heap: Heap,
    pub syms: SymbolTable,
    pub globals: Val,
    pub true_val: Val,
    pub false_val: Val,
    pub void_val: Val,
    pub strict: bool,
    pub macros: Vec<(Val, crate::macros::Macro)>,
    pub ports: Vec<crate::eval::Port>,
    pub stdin_port: Val,
    pub stdout_port: Val,
}

enum State {
    Eval { expr: Val, env: Val, cont: Val },
    ApplyCont { val: Val, cont: Val },
    ApplyProc { proc: Val, args: Val, cont: Val },
    Done(Val),
}

impl CpsEval {
    pub fn new() -> Self {
        let mut heap = Heap::new();
        heap.strict = false; // CPS evaluator uses rib_car/rib_cdr internally
        let syms = SymbolTable::new();
        let true_val = heap.alloc_special(table::TRUE);
        let false_val = heap.alloc_special(table::BOT);
        let void_val = heap.alloc_special(table::VOID);

        let ports = vec![
            crate::eval::Port { buffer: Vec::new(), pos: 0, writer: None, closed: false, direction: 0 },
            crate::eval::Port { buffer: Vec::new(), pos: 0, writer: Some(Box::new(std::io::stdout())), closed: false, direction: 1 },
            crate::eval::Port { buffer: Vec::new(), pos: 0, writer: Some(Box::new(std::io::stderr())), closed: false, direction: 1 },
        ];
        let stdin_port = heap.alloc_rib(Val::fixnum(0), Val::fixnum(0), table::T_PORT);
        let stdout_port = heap.alloc_rib(Val::fixnum(1), Val::fixnum(1), table::T_PORT);

        let mut ev = CpsEval {
            heap, syms, globals: Val::NIL,
            true_val, false_val, void_val,
            strict: false,
            macros: Vec::new(),
            ports,
            stdin_port,
            stdout_port,
        };
        ev.register_builtins();
        ev
    }

    // ── Continuation constructors ────────────────────────────────

    fn k_done(&mut self) -> Val {
        let data = self.heap.cons(Val::fixnum(K_DONE), Val::NIL);
        self.heap.alloc_rib(data, Val::NIL, table::T_CONT)
    }

    fn k_if(&mut self, consequent: Val, alternate: Val, env: Val, k: Val) -> Val {
        let data = self.heap.list(&[Val::fixnum(K_IF), consequent, alternate, env]);
        self.heap.alloc_rib(data, k, table::T_CONT)
    }

    fn k_set(&mut self, var: Val, env: Val, k: Val) -> Val {
        let data = self.heap.list(&[Val::fixnum(K_SET), var, env]);
        self.heap.alloc_rib(data, k, table::T_CONT)
    }

    fn k_define(&mut self, var: Val, k: Val) -> Val {
        let data = self.heap.list(&[Val::fixnum(K_DEFINE), var]);
        self.heap.alloc_rib(data, k, table::T_CONT)
    }

    fn k_begin(&mut self, remaining: Val, env: Val, k: Val) -> Val {
        let data = self.heap.list(&[Val::fixnum(K_BEGIN), remaining, env]);
        self.heap.alloc_rib(data, k, table::T_CONT)
    }

    fn k_evfn(&mut self, arg_exprs: Val, env: Val, k: Val) -> Val {
        let data = self.heap.list(&[Val::fixnum(K_EVFN), arg_exprs, env]);
        self.heap.alloc_rib(data, k, table::T_CONT)
    }

    fn k_evarg(&mut self, remaining: Val, done_rev: Val, proc: Val, env: Val, k: Val) -> Val {
        let data = self.heap.list(&[Val::fixnum(K_EVARG), remaining, done_rev, proc, env]);
        self.heap.alloc_rib(data, k, table::T_CONT)
    }

    fn k_and(&mut self, remaining: Val, env: Val, k: Val) -> Val {
        let data = self.heap.list(&[Val::fixnum(K_AND), remaining, env]);
        self.heap.alloc_rib(data, k, table::T_CONT)
    }

    fn k_or(&mut self, remaining: Val, env: Val, k: Val) -> Val {
        let data = self.heap.list(&[Val::fixnum(K_OR), remaining, env]);
        self.heap.alloc_rib(data, k, table::T_CONT)
    }

    // ── Continuation accessors ───────────────────────────────────

    fn cont_tag(&self, k: Val) -> i64 {
        let data = self.heap.rib_car(k);
        self.heap.car(data).as_fixnum().unwrap_or(-1)
    }

    fn cont_parent(&self, k: Val) -> Val {
        self.heap.rib_cdr(k)
    }

    /// Get nth data field (0 = tag, 1 = first field, ...)
    fn cont_field(&self, k: Val, n: usize) -> Val {
        let mut data = self.heap.rib_car(k);
        for _ in 0..n {
            data = self.heap.cdr(data);
        }
        self.heap.car(data)
    }

    // ── The main loop ────────────────────────────────────────────

    pub fn eval(&mut self, expr: Val, env: Val) -> Val {
        let k = self.k_done();
        let mut state = State::Eval { expr, env, cont: k };

        loop {
            state = match state {
                State::Eval { expr, env, cont } => self.step_eval(expr, env, cont),
                State::ApplyCont { val, cont } => self.step_apply_cont(val, cont),
                State::ApplyProc { proc, args, cont } => self.step_apply_proc(proc, args, cont),
                State::Done(val) => return val,
            };
        }
    }

    fn step_eval(&mut self, expr: Val, env: Val, cont: Val) -> State {
        // Fixnum: self-evaluating
        if expr.is_fixnum() {
            return State::ApplyCont { val: expr, cont };
        }

        // Nil: self-evaluating
        if expr == Val::NIL {
            return State::ApplyCont { val: Val::NIL, cont };
        }

        if !expr.is_rib() {
            return State::ApplyCont { val: Val::NIL, cont };
        }

        let tag = self.heap.tag(expr);

        // Symbol: variable lookup
        if tag == table::T_SYM {
            let val = self.lookup(expr, env).unwrap_or_else(|| {
                let name = self.syms.symbol_name(expr)
                    .unwrap_or("?");
                panic!("unbound variable: {}", name)
            });
            return State::ApplyCont { val, cont };
        }

        // Self-evaluating: canonicalize booleans, pass others through
        if tag == table::TRUE {
            return State::ApplyCont { val: self.true_val, cont };
        }
        if tag == table::BOT {
            return State::ApplyCont { val: self.false_val, cont };
        }
        if tag != table::T_PAIR {
            return State::ApplyCont { val: expr, cont };
        }

        // Pair: special form or procedure call
        let head = self.heap.car(expr);
        let rest = self.heap.cdr(expr);

        if self.heap.is_symbol(head) {
            if self.syms.sym_eq(head, "quote") {
                return State::ApplyCont { val: self.heap.car(rest), cont };
            }

            if self.syms.sym_eq(head, "if") {
                let test = self.heap.car(rest);
                let rest2 = self.heap.cdr(rest);
                let consequent = self.heap.car(rest2);
                let alternate = self.heap.car(self.heap.cdr(rest2));
                let k = self.k_if(consequent, alternate, env, cont);
                return State::Eval { expr: test, env, cont: k };
            }

            if self.syms.sym_eq(head, "define") {
                let target = self.heap.car(rest);
                if self.heap.is_symbol(target) {
                    let val_expr = self.heap.car(self.heap.cdr(rest));
                    let k = self.k_define(target, cont);
                    return State::Eval { expr: val_expr, env, cont: k };
                } else if self.heap.is_pair(target) {
                    let name = self.heap.car(target);
                    let params = self.heap.cdr(target);
                    let body = self.wrap_body(self.heap.cdr(rest));
                    let body_env = self.heap.cons(body, env);
                    let closure = self.heap.closure(params, body_env);
                    self.define_global(name, closure);
                    return State::ApplyCont { val: self.void_val, cont };
                }
            }

            if self.syms.sym_eq(head, "define-syntax") {
                let name_sym = self.heap.car(rest);
                let transformer_expr = self.heap.car(self.heap.cdr(rest));
                if let Some(mac) = crate::macros::parse_syntax_rules(
                    transformer_expr, &self.heap, &self.syms
                ) {
                    self.macros.push((name_sym, mac));
                }
                return State::ApplyCont { val: self.void_val, cont };
            }

            if self.syms.sym_eq(head, "lambda") {
                let params = self.heap.car(rest);
                let body = self.wrap_body(self.heap.cdr(rest));
                let body_env = self.heap.cons(body, env);
                let closure = self.heap.closure(params, body_env);
                return State::ApplyCont { val: closure, cont };
            }

            if self.syms.sym_eq(head, "set!") {
                let var = self.heap.car(rest);
                let val_expr = self.heap.car(self.heap.cdr(rest));
                let k = self.k_set(var, env, cont);
                return State::Eval { expr: val_expr, env, cont: k };
            }

            if self.syms.sym_eq(head, "begin") {
                return self.eval_begin_cps(rest, env, cont);
            }

            if self.syms.sym_eq(head, "and") {
                if rest == Val::NIL {
                    return State::ApplyCont { val: self.true_val, cont };
                }
                let first = self.heap.car(rest);
                let remaining = self.heap.cdr(rest);
                if remaining == Val::NIL {
                    return State::Eval { expr: first, env, cont };
                }
                let k = self.k_and(remaining, env, cont);
                return State::Eval { expr: first, env, cont: k };
            }

            if self.syms.sym_eq(head, "or") {
                if rest == Val::NIL {
                    return State::ApplyCont { val: self.false_val, cont };
                }
                let first = self.heap.car(rest);
                let remaining = self.heap.cdr(rest);
                if remaining == Val::NIL {
                    return State::Eval { expr: first, env, cont };
                }
                let k = self.k_or(remaining, env, cont);
                return State::Eval { expr: first, env, cont: k };
            }

            if self.syms.sym_eq(head, "cond") {
                return self.eval_cond_cps(rest, env, cont);
            }

            if self.syms.sym_eq(head, "let") {
                return self.eval_let_cps(rest, env, cont);
            }

            if self.syms.sym_eq(head, "let*") {
                return self.eval_let_star_cps(rest, env, cont);
            }

            if self.syms.sym_eq(head, "letrec") {
                return self.eval_letrec_cps(rest, env, cont);
            }

            if self.syms.sym_eq(head, "quasiquote") {
                let template = self.heap.car(rest);
                let val = self.expand_quasiquote(template, env);
                return State::ApplyCont { val, cont };
            }
        }

        // Macro expansion
        if self.heap.is_symbol(head) {
            let mac = self.macros.iter().find(|(n, _)| *n == head).map(|(_, m)| m.clone());
            if let Some(mac) = mac {
                if let Some(expanded) = crate::macros::expand_macro(&mac, expr, &mut self.heap, &self.syms) {
                    return State::Eval { expr: expanded, env, cont };
                }
            }
        }

        // Procedure call: evaluate operator, then args
        let k = self.k_evfn(rest, env, cont);
        State::Eval { expr: head, env, cont: k }
    }

    fn step_apply_cont(&mut self, val: Val, cont: Val) -> State {
        match self.cont_tag(cont) {
            K_DONE => State::Done(val),

            K_IF => {
                let consequent = self.cont_field(cont, 1);
                let alternate = self.cont_field(cont, 2);
                let env = self.cont_field(cont, 3);
                let k = self.cont_parent(cont);
                if self.is_true(val) {
                    State::Eval { expr: consequent, env, cont: k }
                } else {
                    State::Eval { expr: alternate, env, cont: k }
                }
            }

            K_SET => {
                let var = self.cont_field(cont, 1);
                let env = self.cont_field(cont, 2);
                let k = self.cont_parent(cont);
                self.set_variable(var, val, env);
                State::ApplyCont { val: self.void_val, cont: k }
            }

            K_DEFINE => {
                let var = self.cont_field(cont, 1);
                let k = self.cont_parent(cont);
                self.define_global(var, val);
                State::ApplyCont { val: self.void_val, cont: k }
            }

            K_BEGIN => {
                let remaining = self.cont_field(cont, 1);
                let env = self.cont_field(cont, 2);
                let k = self.cont_parent(cont);
                // val is the result of the previous expression (ignored)
                self.eval_begin_cps(remaining, env, k)
            }

            K_EVFN => {
                // Operator has been evaluated (val = proc)
                let arg_exprs = self.cont_field(cont, 1);
                let env = self.cont_field(cont, 2);
                let k = self.cont_parent(cont);

                // call/cc special handling
                if val.is_fixnum() && val.as_fixnum() == Some(70) {
                    // (call/cc proc) — eval the single arg, then capture
                    let proc_expr = self.heap.car(arg_exprs);
                    // Build a continuation that will call_cc
                    let _k_cc = self.k_evfn(Val::NIL, env, k);
                    // We mark this as a call/cc by storing the actual cont
                    // in a special way — the arg to call/cc is a proc
                    // that receives the continuation as argument
                    //
                    // Actually, simpler: evaluate the proc arg, then apply
                    // it with the captured continuation as argument
                    let captured_k = k; // this is the continuation to capture
                    let k2 = self.k_evarg(Val::NIL, Val::NIL, Val::fixnum(-1), env, captured_k);
                    return State::Eval { expr: proc_expr, env, cont: k2 };
                }

                if arg_exprs == Val::NIL {
                    // No arguments: apply immediately
                    State::ApplyProc { proc: val, args: Val::NIL, cont: k }
                } else {
                    // Evaluate first argument
                    let first = self.heap.car(arg_exprs);
                    let remaining = self.heap.cdr(arg_exprs);
                    let k2 = self.k_evarg(remaining, Val::NIL, val, env, k);
                    State::Eval { expr: first, env, cont: k2 }
                }
            }

            K_EVARG => {
                // One argument evaluated (val = arg value)
                let remaining = self.cont_field(cont, 1);
                let done_rev = self.cont_field(cont, 2);
                let proc = self.cont_field(cont, 3);
                let env = self.cont_field(cont, 4);
                let k = self.cont_parent(cont);

                let new_done = self.heap.cons(val, done_rev);

                // call/cc sentinel: proc == fixnum(-1) means this is call/cc
                if proc == Val::fixnum(-1) {
                    // val is the proc passed to call/cc
                    // k is the captured continuation
                    // Apply proc with k as argument
                    let cont_obj = self.make_continuation_proc(k);
                    let args = self.heap.cons(cont_obj, Val::NIL);
                    return State::ApplyProc { proc: val, args, cont: k };
                }

                if remaining == Val::NIL {
                    // All arguments evaluated, reverse and apply
                    let args = self.reverse_list(new_done);
                    State::ApplyProc { proc, args, cont: k }
                } else {
                    let first = self.heap.car(remaining);
                    let rest = self.heap.cdr(remaining);
                    let k2 = self.k_evarg(rest, new_done, proc, env, k);
                    State::Eval { expr: first, env, cont: k2 }
                }
            }

            K_AND => {
                let remaining = self.cont_field(cont, 1);
                let env = self.cont_field(cont, 2);
                let k = self.cont_parent(cont);
                if !self.is_true(val) {
                    State::ApplyCont { val, cont: k }
                } else if remaining == Val::NIL {
                    State::ApplyCont { val, cont: k }
                } else {
                    let first = self.heap.car(remaining);
                    let rest = self.heap.cdr(remaining);
                    if rest == Val::NIL {
                        State::Eval { expr: first, env, cont: k }
                    } else {
                        let k2 = self.k_and(rest, env, k);
                        State::Eval { expr: first, env, cont: k2 }
                    }
                }
            }

            K_OR => {
                let remaining = self.cont_field(cont, 1);
                let env = self.cont_field(cont, 2);
                let k = self.cont_parent(cont);
                if self.is_true(val) {
                    State::ApplyCont { val, cont: k }
                } else if remaining == Val::NIL {
                    State::ApplyCont { val, cont: k }
                } else {
                    let first = self.heap.car(remaining);
                    let rest = self.heap.cdr(remaining);
                    if rest == Val::NIL {
                        State::Eval { expr: first, env, cont: k }
                    } else {
                        let k2 = self.k_or(rest, env, k);
                        State::Eval { expr: first, env, cont: k2 }
                    }
                }
            }

            _ => State::Done(val),
        }
    }

    fn step_apply_proc(&mut self, proc: Val, args: Val, cont: Val) -> State {
        if self.heap.is_closure(proc) {
            let params = self.heap.rib_car(proc);
            let body_env = self.heap.rib_cdr(proc);
            let body = self.heap.car(body_env);
            let closed_env = self.heap.cdr(body_env);
            let env = self.extend_env(params, args, closed_env);
            State::Eval { expr: body, env, cont }
        } else if proc.is_fixnum() {
            let id = proc.as_fixnum().unwrap();

            // Continuation invocation (negative id)
            if id < 0 {
                let val = self.heap.car(args);
                // Find the saved continuation from the proc
                // The continuation proc stores its k in its closure env
                // But we encoded it differently — we need to handle this
                // via the continuation object
                return State::Done(val); // fallback for now
            }

            let val = self.apply_builtin(proc, args);
            State::ApplyCont { val, cont }
        } else if self.heap.tag(proc) == table::T_CONT {
            // Invoking a captured continuation!
            // The continuation-as-procedure wraps a real continuation.
            // car = the saved continuation, cdr = NIL, tag = T_CONT
            // Wait, we need to distinguish cont-as-proc from cont frames.
            // Let's check: cont-as-proc has its car as a "marker"
            let saved_k = self.heap.rib_car(proc);
            let val = self.heap.car(args);
            State::ApplyCont { val, cont: saved_k }
        } else {
            State::ApplyCont { val: Val::NIL, cont }
        }
    }

    // ── Continuation as procedure (for call/cc) ──────────────────

    fn make_continuation_proc(&mut self, k: Val) -> Val {
        // Wrap a continuation as a callable procedure.
        // We store it as a rib with T_CONT tag but distinguishable
        // from regular cont frames by having the saved cont directly as car.
        // When invoked in step_apply_proc, we detect T_CONT tag and
        // restore the saved continuation.
        //
        // To distinguish from a continuation frame: cont frames have
        // a data *list* as car (first element is a fixnum tag).
        // Cont-as-proc has the saved continuation rib directly as car.
        self.heap.alloc_rib(k, Val::fixnum(-1), table::T_CONT)
    }

    // ── Helper: begin in CPS ─────────────────────────────────────

    fn eval_begin_cps(&mut self, exprs: Val, env: Val, cont: Val) -> State {
        if exprs == Val::NIL {
            return State::ApplyCont { val: self.void_val, cont };
        }
        let first = self.heap.car(exprs);
        let remaining = self.heap.cdr(exprs);
        if remaining == Val::NIL {
            // Last expression: tail position
            State::Eval { expr: first, env, cont }
        } else {
            let k = self.k_begin(remaining, env, cont);
            State::Eval { expr: first, env, cont: k }
        }
    }

    // ── Helper: cond in CPS ──────────────────────────────────────

    fn eval_cond_cps(&mut self, clauses: Val, env: Val, cont: Val) -> State {
        if !self.heap.is_pair(clauses) {
            return State::ApplyCont { val: self.void_val, cont };
        }
        let clause = self.heap.car(clauses);
        let test_expr = self.heap.car(clause);
        let body = self.heap.cdr(clause);

        if self.heap.is_symbol(test_expr) && self.syms.sym_eq(test_expr, "else") {
            return self.eval_begin_cps(body, env, cont);
        }

        // Evaluate test, with a continuation that checks the result
        // and either executes the body or tries the next clause.
        // We reuse K_IF: if true → begin body, if false → next clause
        let body_expr = if body == Val::NIL {
            // (cond (test) ...) — return test value
            // We need a way to return the test value itself...
            // For now, wrap in a begin
            test_expr
        } else {
            self.wrap_body_list(body)
        };
        let remaining_clauses = self.heap.cdr(clauses);
        let else_expr = self.wrap_cond(remaining_clauses);
        let k = self.k_if(body_expr, else_expr, env, cont);
        State::Eval { expr: test_expr, env, cont: k }
    }

    fn wrap_cond(&mut self, clauses: Val) -> Val {
        if !self.heap.is_pair(clauses) {
            return self.void_val;
        }
        let cond_sym = self.syms.intern("cond", &mut self.heap);
        self.heap.cons(cond_sym, clauses)
    }

    // ── Helper: let/let*/letrec in CPS ───────────────────────────

    fn eval_let_cps(&mut self, rest: Val, env: Val, cont: Val) -> State {
        let first = self.heap.car(rest);

        // Named let
        if self.heap.is_symbol(first) {
            let name = first;
            let bindings = self.heap.car(self.heap.cdr(rest));
            let body_exprs = self.heap.cdr(self.heap.cdr(rest));

            let mut params = Vec::new();
            let mut inits = Vec::new();
            let mut b = bindings;
            while self.heap.is_pair(b) {
                let binding = self.heap.car(b);
                params.push(self.heap.car(binding));
                inits.push(self.heap.car(self.heap.cdr(binding)));
                b = self.heap.cdr(b);
            }

            let param_list = self.heap.list(&params);
            let body = self.wrap_body(body_exprs);
            let body_env = self.heap.cons(body, env);
            let closure = self.heap.closure(param_list, body_env);

            let binding = self.heap.cons(name, closure);
            let rec_env = self.heap.cons(binding, env);
            let new_body_env = self.heap.cons(body, rec_env);
            self.heap.set_cdr_raw(closure, new_body_env);

            // Evaluate init expressions and apply
            let call = self.build_call(name, &inits);
            return State::Eval { expr: call, env: rec_env, cont };
        }

        // Regular let: desugar to lambda application
        let bindings = first;
        let body_exprs = self.heap.cdr(rest);

        let mut params = Vec::new();
        let mut init_exprs = Vec::new();
        let mut b = bindings;
        while self.heap.is_pair(b) {
            let binding = self.heap.car(b);
            params.push(self.heap.car(binding));
            init_exprs.push(self.heap.car(self.heap.cdr(binding)));
            b = self.heap.cdr(b);
        }

        // Build ((lambda (params...) body) init-exprs...)
        let param_list = self.heap.list(&params);
        let body = self.wrap_body(body_exprs);
        let body_env_rib = self.heap.cons(body, env);
        let closure = self.heap.closure(param_list, body_env_rib);

        // Evaluate init expressions
        let _args_list = self.heap.list(&init_exprs);
        if init_exprs.is_empty() {
            State::ApplyProc { proc: closure, args: Val::NIL, cont }
        } else {
            let first_init = init_exprs[0];
            let remaining = self.heap.list(&init_exprs[1..]);
            let k = self.k_evarg(remaining, Val::NIL, closure, env, cont);
            State::Eval { expr: first_init, env, cont: k }
        }
    }

    fn eval_let_star_cps(&mut self, rest: Val, env: Val, cont: Val) -> State {
        let bindings = self.heap.car(rest);
        let body_exprs = self.heap.cdr(rest);

        // Desugar to nested lets
        if !self.heap.is_pair(bindings) {
            return self.eval_begin_cps(body_exprs, env, cont);
        }

        let first_binding = self.heap.car(bindings);
        let remaining = self.heap.cdr(bindings);
        let var = self.heap.car(first_binding);
        let init_expr = self.heap.car(self.heap.cdr(first_binding));

        // After evaluating init, bind and continue with remaining let*
        // This is like: evaluate init, then extend env and process rest
        if !self.heap.is_pair(remaining) {
            // Last binding: bind and eval body
            let body = self.wrap_body(body_exprs);
            let param_list = self.heap.cons(var, Val::NIL);
            let body_env_rib = self.heap.cons(body, env);
            let closure = self.heap.closure(param_list, body_env_rib);
            let k = self.k_evarg(Val::NIL, Val::NIL, closure, env, cont);
            State::Eval { expr: init_expr, env, cont: k }
        } else {
            // More bindings: wrap in a lambda that does the next let*
            let inner_let_star = {
                let ls_sym = self.syms.intern("let*", &mut self.heap);
                let inner = self.heap.cons(remaining, body_exprs);
                self.heap.cons(ls_sym, inner)
            };
            let param_list = self.heap.cons(var, Val::NIL);
            let body_env_rib = self.heap.cons(inner_let_star, env);
            let closure = self.heap.closure(param_list, body_env_rib);
            let k = self.k_evarg(Val::NIL, Val::NIL, closure, env, cont);
            State::Eval { expr: init_expr, env, cont: k }
        }
    }

    fn eval_letrec_cps(&mut self, rest: Val, env: Val, cont: Val) -> State {
        let bindings = self.heap.car(rest);
        let body_exprs = self.heap.cdr(rest);

        // Bind all names to NIL first
        let mut new_env = env;
        let mut b = bindings;
        let mut vars = Vec::new();
        let mut init_exprs = Vec::new();
        while self.heap.is_pair(b) {
            let binding = self.heap.car(b);
            let var = self.heap.car(binding);
            let init = self.heap.car(self.heap.cdr(binding));
            let pair = self.heap.cons(var, Val::NIL);
            new_env = self.heap.cons(pair, new_env);
            vars.push(var);
            init_exprs.push(init);
            b = self.heap.cdr(b);
        }

        // Evaluate inits in new_env and set! each
        // Build: (begin (set! v1 init1) (set! v2 init2) ... body...)
        let set_sym = self.syms.intern("set!", &mut self.heap);
        let mut stmts = Vec::new();
        for (var, init) in vars.iter().zip(init_exprs.iter()) {
            let set_expr = self.heap.list(&[set_sym, *var, *init]);
            stmts.push(set_expr);
        }
        // Add body expressions
        let mut body = body_exprs;
        while self.heap.is_pair(body) {
            stmts.push(self.heap.car(body));
            body = self.heap.cdr(body);
        }

        let begin_body = self.heap.list(&stmts);
        self.eval_begin_cps(begin_body, new_env, cont)
    }

    // ── Helpers ──────────────────────────────────────────────────

    fn wrap_body(&mut self, body_exprs: Val) -> Val {
        if self.heap.cdr(body_exprs) == Val::NIL {
            self.heap.car(body_exprs)
        } else {
            let begin_sym = self.syms.intern("begin", &mut self.heap);
            self.heap.cons(begin_sym, body_exprs)
        }
    }

    fn wrap_body_list(&mut self, body: Val) -> Val {
        if self.heap.cdr(body) == Val::NIL {
            self.heap.car(body)
        } else {
            let begin_sym = self.syms.intern("begin", &mut self.heap);
            self.heap.cons(begin_sym, body)
        }
    }

    fn build_call(&mut self, func: Val, args: &[Val]) -> Val {
        let arg_list = self.heap.list(args);
        self.heap.cons(func, arg_list)
    }

    fn reverse_list(&mut self, mut lst: Val) -> Val {
        let mut result = Val::NIL;
        while self.heap.is_pair(lst) {
            result = self.heap.cons(self.heap.car(lst), result);
            lst = self.heap.cdr(lst);
        }
        result
    }

    pub fn is_true(&self, v: Val) -> bool {
        // R4RS: only #f is false. '() is truthy.
        if v.is_rib() && self.heap.tag(v) == table::BOT { return false; }
        true
    }

    pub fn scheme_bool(&mut self, b: bool) -> Val {
        if b { self.true_val } else { self.false_val }
    }

    fn expand_quasiquote(&mut self, template: Val, env: Val) -> Val {
        if !self.heap.is_pair(template) {
            return template;
        }
        let head = self.heap.car(template);
        if self.heap.is_symbol(head) && self.syms.sym_eq(head, "unquote") {
            let expr = self.heap.car(self.heap.cdr(template));
            return self.eval(expr, env);
        }
        if self.heap.is_pair(head) {
            let hh = self.heap.car(head);
            if self.heap.is_symbol(hh) && self.syms.sym_eq(hh, "unquote-splicing") {
                let expr = self.heap.car(self.heap.cdr(head));
                let spliced = self.eval(expr, env);
                let rest = self.expand_quasiquote(self.heap.cdr(template), env);
                return self.append(spliced, rest);
            }
        }
        let car = self.expand_quasiquote(head, env);
        let cdr = self.expand_quasiquote(self.heap.cdr(template), env);
        self.heap.cons(car, cdr)
    }

    fn append(&mut self, a: Val, b: Val) -> Val {
        if !self.heap.is_pair(a) { return b; }
        let car = self.heap.car(a);
        let rest = self.append(self.heap.cdr(a), b);
        self.heap.cons(car, rest)
    }

    // ── Environment ──────────────────────────────────────────────

    fn lookup(&self, sym: Val, env: Val) -> Option<Val> {
        let mut e = env;
        while self.heap.is_pair(e) {
            let binding = self.heap.car(e);
            if self.heap.is_pair(binding) && self.heap.car(binding) == sym {
                return Some(self.heap.cdr(binding));
            }
            e = self.heap.cdr(e);
        }
        let mut g = self.globals;
        while self.heap.is_pair(g) {
            let binding = self.heap.car(g);
            if self.heap.is_pair(binding) && self.heap.car(binding) == sym {
                return Some(self.heap.cdr(binding));
            }
            g = self.heap.cdr(g);
        }
        None
    }

    fn define_global(&mut self, sym: Val, val: Val) {
        let mut g = self.globals;
        while self.heap.is_pair(g) {
            let binding = self.heap.car(g);
            if self.heap.is_pair(binding) && self.heap.car(binding) == sym {
                self.heap.set_cdr(binding, val);
                return;
            }
            g = self.heap.cdr(g);
        }
        let binding = self.heap.cons(sym, val);
        self.globals = self.heap.cons(binding, self.globals);
    }

    fn set_variable(&mut self, sym: Val, val: Val, env: Val) {
        let mut e = env;
        while self.heap.is_pair(e) {
            let binding = self.heap.car(e);
            if self.heap.is_pair(binding) && self.heap.car(binding) == sym {
                self.heap.set_cdr(binding, val);
                return;
            }
            e = self.heap.cdr(e);
        }
        let mut g = self.globals;
        while self.heap.is_pair(g) {
            let binding = self.heap.car(g);
            if self.heap.is_pair(binding) && self.heap.car(binding) == sym {
                self.heap.set_cdr(binding, val);
                return;
            }
            g = self.heap.cdr(g);
        }
        self.define_global(sym, val);
    }

    fn extend_env(&mut self, params: Val, args: Val, env: Val) -> Val {
        let mut p = params;
        let mut a = args;
        let mut new_env = env;
        while self.heap.is_pair(p) {
            let param = self.heap.car(p);
            let arg = if self.heap.is_pair(a) {
                let v = self.heap.car(a);
                a = self.heap.cdr(a);
                v
            } else {
                Val::NIL
            };
            let binding = self.heap.cons(param, arg);
            new_env = self.heap.cons(binding, new_env);
            p = self.heap.cdr(p);
        }
        if self.heap.is_symbol(p) {
            let binding = self.heap.cons(p, a);
            new_env = self.heap.cons(binding, new_env);
        }
        new_env
    }

    pub fn intern(&mut self, name: &str) -> Val {
        self.syms.intern(name, &mut self.heap)
    }

    // ── Builtins (reuse from eval.rs via delegation) ─────────────

    fn register_builtins(&mut self) {
        let builtins = [
            ("+", 0), ("-", 1), ("*", 2), ("quotient", 3),
            ("remainder", 4), ("modulo", 5),
            ("=", 6), ("<", 7), (">", 8), ("<=", 9), (">=", 10),
            ("cons", 11), ("car", 12), ("cdr", 13),
            ("set-car!", 14), ("set-cdr!", 15),
            ("null?", 16), ("pair?", 17), ("number?", 18),
            ("symbol?", 19), ("string?", 20), ("vector?", 21),
            ("char?", 22), ("procedure?", 23), ("boolean?", 24),
            ("not", 25), ("eq?", 26), ("equal?", 27), ("eqv?", 28),
            ("list", 29), ("length", 30), ("append", 31),
            ("display", 32), ("newline", 33), ("write", 34),
            ("zero?", 35), ("positive?", 36), ("negative?", 37),
            ("even?", 38), ("odd?", 39),
            ("abs", 40), ("max", 41), ("min", 42),
            ("gcd", 43), ("map", 44), ("for-each", 45),
            ("apply", 46),
            ("char->integer", 47), ("integer->char", 48),
            ("number->string", 49), ("string->number", 50),
            ("string-length", 51), ("string-ref", 52),
            ("string-append", 53),
            ("vector-length", 54), ("vector-ref", 55), ("vector-set!", 56),
            ("make-vector", 57), ("make-string", 58),
            ("symbol->string", 59), ("string->symbol", 60),
            ("reverse", 61),
            ("list-ref", 62), ("list-tail", 63),
            ("memq", 64), ("memv", 65), ("member", 66),
            ("assq", 67), ("assv", 68), ("assoc", 69),
            ("call-with-current-continuation", 70),
            ("force", 71), ("/", 72), ("lcm", 73),
            ("expt", 94),
            ("integer?", 91), ("exact?", 92),
            ("eof-object?", 101),
            ("error", 103),
            // Char comparisons (case-sensitive)
            ("char=?", 81), ("char<?", 82), ("char>?", 98),
            ("char<=?", 99), ("char>=?", 100),
            ("char-alphabetic?", 83), ("char-numeric?", 84),
            ("char-whitespace?", 85), ("char-upper-case?", 86),
            ("char-lower-case?", 87), ("char-upcase", 88), ("char-downcase", 89),
            // String comparisons (case-sensitive)
            ("string=?", 74), ("string<?", 75),
            ("string>?", 95), ("string<=?", 96), ("string>=?", 97),
            ("string-length", 51), ("string-ref", 52),
            ("string-append", 53), ("make-string", 58),
            ("substring", 76), ("string-set!", 90),
            // Case-insensitive char comparisons
            ("char-ci=?", 104), ("char-ci<?", 105), ("char-ci>?", 106),
            ("char-ci<=?", 107), ("char-ci>=?", 108),
            // Case-insensitive string comparisons
            ("string-ci=?", 109), ("string-ci<?", 110), ("string-ci>?", 111),
            ("string-ci<=?", 112), ("string-ci>=?", 113),
            // Port / I/O
            ("open-input-file", 120), ("open-output-file", 121),
            ("close-input-port", 122), ("close-output-port", 123),
            ("current-input-port", 124), ("current-output-port", 125),
            ("input-port?", 126), ("output-port?", 127),
            ("read", 130), ("load", 131),
            ("read-char", 132), ("peek-char", 133), ("port?", 134),
            // ── Algebra extension (wispy algebra) ────────────
            ("dot", 200),       // (dot a b) → CAYLEY[a][b]
            ("tau", 201),       // (tau x) → type tag of x
            ("type-valid?", 202), // (type-valid? op tag) → #t if not BOT
            ("strict-mode", 203),    // type errors panic
            ("permissive-mode", 204), // type errors return NIL (default)
        ];
        for (name, id) in builtins {
            let sym = self.syms.intern(name, &mut self.heap);
            self.define_global(sym, Val::fixnum(id));
        }

        // Algebra element constants
        let elements = [
            ("TOP", table::TOP), ("BOT", table::BOT),
            ("Q", table::Q), ("E", table::E),
            ("CAR", table::CAR), ("CDR", table::CDR), ("CONS", table::CONS),
            ("RHO", table::RHO), ("APPLY", table::APPLY), ("CC", table::CC),
            ("TAU", table::TAU), ("Y", table::Y),
            ("T_PAIR", table::T_PAIR), ("T_SYM", table::T_SYM),
            ("T_CLS", table::T_CLS), ("T_STR", table::T_STR),
            ("T_VEC", table::T_VEC), ("T_CHAR", table::T_CHAR),
            ("T_CONT", table::T_CONT), ("T_PORT", table::T_PORT),
            ("TRUE", table::TRUE), ("EOF", table::EOF), ("VOID", table::VOID),
        ];
        for (name, elem) in elements {
            let sym = self.syms.intern(name, &mut self.heap);
            self.define_global(sym, Val::fixnum(elem as i64));
        }
    }

    fn apply_builtin(&mut self, id: Val, args: Val) -> Val {
        let id = id.as_fixnum().unwrap();
        let a1 = self.heap.car(args);
        let a2 = self.heap.car(self.heap.cdr(args));

        match id {
            0 => { let mut s = 0i64; let mut a = args;
                   while self.heap.is_pair(a) { s += self.heap.car(a).as_fixnum().unwrap_or(0); a = self.heap.cdr(a); }
                   Val::fixnum(s) }
            1 => { if self.heap.cdr(args) == Val::NIL { Val::fixnum(-a1.as_fixnum().unwrap_or(0)) }
                   else { let mut r = a1.as_fixnum().unwrap_or(0); let mut a = self.heap.cdr(args);
                          while self.heap.is_pair(a) { r -= self.heap.car(a).as_fixnum().unwrap_or(0); a = self.heap.cdr(a); }
                          Val::fixnum(r) } }
            2 => { let mut p = 1i64; let mut a = args;
                   while self.heap.is_pair(a) { p *= self.heap.car(a).as_fixnum().unwrap_or(0); a = self.heap.cdr(a); }
                   Val::fixnum(p) }
            3 => Val::fixnum(a1.as_fixnum().unwrap_or(0) / a2.as_fixnum().unwrap_or(1)),
            4 => Val::fixnum(a1.as_fixnum().unwrap_or(0) % a2.as_fixnum().unwrap_or(1)),
            5 => { let (a,b) = (a1.as_fixnum().unwrap_or(0), a2.as_fixnum().unwrap_or(1)); Val::fixnum(((a%b)+b)%b) }
            6 => self.scheme_bool(a1.as_fixnum() == a2.as_fixnum()),
            7 => self.scheme_bool(a1.as_fixnum() < a2.as_fixnum()),
            8 => self.scheme_bool(a1.as_fixnum() > a2.as_fixnum()),
            9 => self.scheme_bool(a1.as_fixnum() <= a2.as_fixnum()),
            10 => self.scheme_bool(a1.as_fixnum() >= a2.as_fixnum()),
            11 => self.heap.cons(a1, a2),
            12 => self.heap.car(a1),
            13 => self.heap.cdr(a1),
            14 => { self.heap.set_car(a1, a2); self.void_val }
            15 => { self.heap.set_cdr(a1, a2); self.void_val }
            16 => self.scheme_bool(a1 == Val::NIL),
            17 => self.scheme_bool(self.heap.is_pair(a1)),
            18 => self.scheme_bool(a1.is_fixnum()),
            19 => self.scheme_bool(self.heap.is_symbol(a1)),
            20 => self.scheme_bool(self.heap.is_string(a1)),
            21 => self.scheme_bool(self.heap.is_vector(a1)),
            22 => self.scheme_bool(self.heap.tag(a1) == table::T_CHAR),
            23 => self.scheme_bool(self.heap.is_closure(a1) || a1.is_fixnum() || self.heap.tag(a1) == table::T_CONT),
            24 => self.scheme_bool(a1 == self.true_val || a1 == self.false_val || self.heap.tag(a1) == table::TRUE || self.heap.tag(a1) == table::BOT),
            25 => self.scheme_bool(!self.is_true(a1)),
            26 | 28 => self.scheme_bool(a1 == a2),
            27 => self.scheme_bool(self.equal(a1, a2)),
            29 => args,
            30 => Val::fixnum(self.heap.length(a1) as i64),
            31 => self.append(a1, a2),
            32 => { self.display(a1); self.void_val }
            33 => { println!(); self.void_val }
            34 => { self.display(a1); self.void_val } // simplified write
            35 => self.scheme_bool(a1.as_fixnum() == Some(0)),
            36 => self.scheme_bool(a1.as_fixnum().map_or(false, |n| n > 0)),
            37 => self.scheme_bool(a1.as_fixnum().map_or(false, |n| n < 0)),
            38 => self.scheme_bool(a1.as_fixnum().map_or(false, |n| n % 2 == 0)),
            39 => self.scheme_bool(a1.as_fixnum().map_or(false, |n| n % 2 != 0)),
            40 => Val::fixnum(a1.as_fixnum().unwrap_or(0).abs()),
            41 => Val::fixnum(a1.as_fixnum().unwrap_or(0).max(a2.as_fixnum().unwrap_or(0))),
            42 => Val::fixnum(a1.as_fixnum().unwrap_or(0).min(a2.as_fixnum().unwrap_or(0))),
            43 => { let (mut a, mut b) = (a1.as_fixnum().unwrap_or(0).abs(), a2.as_fixnum().unwrap_or(0).abs());
                    while b != 0 { let t = b; b = a % b; a = t; } Val::fixnum(a) }
            44 => self.builtin_map(a1, a2),
            45 => { self.builtin_for_each(a1, a2); self.void_val }
            46 => { // apply: (apply proc args)
                   self.apply_proc_sync(a1, a2) }
            47 => { let cp = self.heap.rib_car(a1).as_fixnum().unwrap_or(0); Val::fixnum(cp) }
            48 => self.heap.character(a1.as_fixnum().unwrap_or(0)),
            49 => { let n = a1.as_fixnum().unwrap_or(0); self.make_string(&format!("{n}")) }
            51 => self.heap.rib_cdr(a1),
            59 => self.heap.rib_car(a1),
            60 => { if let Some(name) = self.extract_string(a1) { self.syms.intern(&name, &mut self.heap) } else { Val::NIL } }
            61 => self.reverse_list(a1),
            62 => { let idx = a2.as_fixnum().unwrap_or(0); let mut l = a1; for _ in 0..idx { l = self.heap.cdr(l); } self.heap.car(l) }
            63 => { let idx = a2.as_fixnum().unwrap_or(0); let mut l = a1; for _ in 0..idx { l = self.heap.cdr(l); } l }
            72 => { let b = a2.as_fixnum().unwrap_or(1); if b == 0 { Val::NIL } else { Val::fixnum(a1.as_fixnum().unwrap_or(0) / b) } }
            91 | 92 => self.scheme_bool(a1.is_fixnum()),
            94 => { let base = a1.as_fixnum().unwrap_or(0); let exp = a2.as_fixnum().unwrap_or(0);
                    let mut r = 1i64; for _ in 0..exp { r *= base; } Val::fixnum(r) }
            101 => self.scheme_bool(self.heap.tag(a1) == table::EOF),
            103 => { eprintln!("Error"); Val::NIL }

            // Char comparisons (case-sensitive)
            81 => { let ca = self.heap.rib_car(a1).as_fixnum(); let cb = self.heap.rib_car(a2).as_fixnum(); self.scheme_bool(ca == cb) }
            82 => { let ca = self.heap.rib_car(a1).as_fixnum().unwrap_or(0); let cb = self.heap.rib_car(a2).as_fixnum().unwrap_or(0); self.scheme_bool(ca < cb) }
            83 => { let cp = self.heap.rib_car(a1).as_fixnum().unwrap_or(0) as u8; self.scheme_bool(cp.is_ascii_alphabetic()) }
            84 => { let cp = self.heap.rib_car(a1).as_fixnum().unwrap_or(0) as u8; self.scheme_bool(cp.is_ascii_digit()) }
            85 => { let cp = self.heap.rib_car(a1).as_fixnum().unwrap_or(0) as u8; self.scheme_bool(cp.is_ascii_whitespace()) }
            86 => { let cp = self.heap.rib_car(a1).as_fixnum().unwrap_or(0) as u8; self.scheme_bool(cp.is_ascii_uppercase()) }
            87 => { let cp = self.heap.rib_car(a1).as_fixnum().unwrap_or(0) as u8; self.scheme_bool(cp.is_ascii_lowercase()) }
            88 => { let cp = self.heap.rib_car(a1).as_fixnum().unwrap_or(0) as u8; self.heap.character(cp.to_ascii_uppercase() as i64) }
            89 => { let cp = self.heap.rib_car(a1).as_fixnum().unwrap_or(0) as u8; self.heap.character(cp.to_ascii_lowercase() as i64) }
            90 => { // string-set!
                let idx = a2.as_fixnum().unwrap_or(0);
                let a3 = self.heap.car(self.heap.cdr(self.heap.cdr(args)));
                let cp = self.heap.rib_car(a3).as_fixnum().unwrap_or(0);
                let mut chars = self.heap.rib_car(a1);
                for _ in 0..idx { chars = self.heap.cdr(chars); }
                self.heap.set_car(chars, Val::fixnum(cp));
                self.void_val
            }
            95 => { let sa = self.extract_string(a1).unwrap_or_default(); let sb = self.extract_string(a2).unwrap_or_default(); self.scheme_bool(sa > sb) }
            96 => { let sa = self.extract_string(a1).unwrap_or_default(); let sb = self.extract_string(a2).unwrap_or_default(); self.scheme_bool(sa <= sb) }
            97 => { let sa = self.extract_string(a1).unwrap_or_default(); let sb = self.extract_string(a2).unwrap_or_default(); self.scheme_bool(sa >= sb) }
            98 => { let ca = self.heap.rib_car(a1).as_fixnum().unwrap_or(0); let cb = self.heap.rib_car(a2).as_fixnum().unwrap_or(0); self.scheme_bool(ca > cb) }
            99 => { let ca = self.heap.rib_car(a1).as_fixnum().unwrap_or(0); let cb = self.heap.rib_car(a2).as_fixnum().unwrap_or(0); self.scheme_bool(ca <= cb) }
            100 => { let ca = self.heap.rib_car(a1).as_fixnum().unwrap_or(0); let cb = self.heap.rib_car(a2).as_fixnum().unwrap_or(0); self.scheme_bool(ca >= cb) }

            // String operations
            52 => { // string-ref
                let idx = a2.as_fixnum().unwrap_or(0);
                let mut chars = self.heap.rib_car(a1);
                for _ in 0..idx { chars = self.heap.cdr(chars); }
                self.heap.character(self.heap.car(chars).as_fixnum().unwrap_or(0))
            }
            53 => { // string-append
                let s1 = self.extract_string(a1).unwrap_or_default();
                let s2 = self.extract_string(a2).unwrap_or_default();
                self.make_string(&format!("{s1}{s2}"))
            }
            58 => { // make-string
                let len = a1.as_fixnum().unwrap_or(0);
                let fill = if a2.is_fixnum() { a2.as_fixnum().unwrap_or(b' ' as i64) }
                           else { self.heap.rib_car(a2).as_fixnum().unwrap_or(b' ' as i64) };
                let mut chars = Val::NIL;
                for _ in 0..len { chars = self.heap.cons(Val::fixnum(fill), chars); }
                self.heap.string(chars, Val::fixnum(len))
            }
            74 => { let sa = self.extract_string(a1).unwrap_or_default(); let sb = self.extract_string(a2).unwrap_or_default(); self.scheme_bool(sa == sb) }
            75 => { let sa = self.extract_string(a1).unwrap_or_default(); let sb = self.extract_string(a2).unwrap_or_default(); self.scheme_bool(sa < sb) }
            76 => { // substring
                let s = self.extract_string(a1).unwrap_or_default();
                let start = a2.as_fixnum().unwrap_or(0) as usize;
                let a3 = self.heap.car(self.heap.cdr(self.heap.cdr(args)));
                let end = a3.as_fixnum().unwrap_or(s.len() as i64) as usize;
                self.make_string(&s[start..end])
            }

            // Case-insensitive char comparisons
            104 => { let ca = (self.heap.rib_car(a1).as_fixnum().unwrap_or(0) as u8).to_ascii_lowercase();
                     let cb = (self.heap.rib_car(a2).as_fixnum().unwrap_or(0) as u8).to_ascii_lowercase(); self.scheme_bool(ca == cb) }
            105 => { let ca = (self.heap.rib_car(a1).as_fixnum().unwrap_or(0) as u8).to_ascii_lowercase();
                     let cb = (self.heap.rib_car(a2).as_fixnum().unwrap_or(0) as u8).to_ascii_lowercase(); self.scheme_bool(ca < cb) }
            106 => { let ca = (self.heap.rib_car(a1).as_fixnum().unwrap_or(0) as u8).to_ascii_lowercase();
                     let cb = (self.heap.rib_car(a2).as_fixnum().unwrap_or(0) as u8).to_ascii_lowercase(); self.scheme_bool(ca > cb) }
            107 => { let ca = (self.heap.rib_car(a1).as_fixnum().unwrap_or(0) as u8).to_ascii_lowercase();
                     let cb = (self.heap.rib_car(a2).as_fixnum().unwrap_or(0) as u8).to_ascii_lowercase(); self.scheme_bool(ca <= cb) }
            108 => { let ca = (self.heap.rib_car(a1).as_fixnum().unwrap_or(0) as u8).to_ascii_lowercase();
                     let cb = (self.heap.rib_car(a2).as_fixnum().unwrap_or(0) as u8).to_ascii_lowercase(); self.scheme_bool(ca >= cb) }

            // Case-insensitive string comparisons
            109 => { let sa = self.extract_string(a1).unwrap_or_default().to_ascii_lowercase();
                     let sb = self.extract_string(a2).unwrap_or_default().to_ascii_lowercase(); self.scheme_bool(sa == sb) }
            110 => { let sa = self.extract_string(a1).unwrap_or_default().to_ascii_lowercase();
                     let sb = self.extract_string(a2).unwrap_or_default().to_ascii_lowercase(); self.scheme_bool(sa < sb) }
            111 => { let sa = self.extract_string(a1).unwrap_or_default().to_ascii_lowercase();
                     let sb = self.extract_string(a2).unwrap_or_default().to_ascii_lowercase(); self.scheme_bool(sa > sb) }
            112 => { let sa = self.extract_string(a1).unwrap_or_default().to_ascii_lowercase();
                     let sb = self.extract_string(a2).unwrap_or_default().to_ascii_lowercase(); self.scheme_bool(sa <= sb) }
            113 => { let sa = self.extract_string(a1).unwrap_or_default().to_ascii_lowercase();
                     let sb = self.extract_string(a2).unwrap_or_default().to_ascii_lowercase(); self.scheme_bool(sa >= sb) }

            // ── Port / I/O builtins ───────────────────────────
            120 => { // open-input-file
                let filename = self.extract_string(a1).unwrap_or_default();
                let content = std::fs::read(&filename).unwrap_or_default();
                let id = self.ports.len();
                self.ports.push(crate::eval::Port {
                    buffer: content, pos: 0, writer: None, closed: false, direction: 0,
                });
                self.heap.alloc_rib(Val::fixnum(id as i64), Val::fixnum(0), table::T_PORT)
            }
            121 => { // open-output-file
                let filename = self.extract_string(a1).unwrap_or_default();
                let file = std::fs::File::create(&filename).unwrap();
                let id = self.ports.len();
                self.ports.push(crate::eval::Port {
                    buffer: Vec::new(), pos: 0,
                    writer: Some(Box::new(std::io::BufWriter::new(file))),
                    closed: false, direction: 1,
                });
                self.heap.alloc_rib(Val::fixnum(id as i64), Val::fixnum(1), table::T_PORT)
            }
            122 | 123 => { // close-input-port / close-output-port
                if let Some(id) = self.heap.rib_car(a1).as_fixnum().map(|n| n as usize) {
                    if id < self.ports.len() {
                        if let Some(w) = &mut self.ports[id].writer {
                            use std::io::Write;
                            let _ = w.flush();
                        }
                        self.ports[id].closed = true;
                    }
                }
                self.void_val
            }
            124 => self.stdin_port,
            125 => self.stdout_port,
            126 => { // input-port?
                self.scheme_bool(self.heap.tag(a1) == table::T_PORT
                    && self.heap.rib_cdr(a1).as_fixnum() == Some(0))
            }
            127 => { // output-port?
                self.scheme_bool(self.heap.tag(a1) == table::T_PORT
                    && self.heap.rib_cdr(a1).as_fixnum() == Some(1))
            }
            130 => { // read
                let pid = if a1 != Val::NIL && self.heap.tag(a1) == table::T_PORT {
                    self.heap.rib_car(a1).as_fixnum().unwrap_or(0) as usize
                } else { 0 };
                if pid == 0 {
                    // stdin: read a line
                    let mut line = String::new();
                    match std::io::stdin().read_line(&mut line) {
                        Ok(0) | Err(_) => self.heap.alloc_special(table::EOF),
                        _ => match crate::reader::read(&line, &mut self.heap, &mut self.syms) {
                            Ok(val) => val,
                            _ => self.heap.alloc_special(table::EOF),
                        }
                    }
                } else {
                    let port = &self.ports[pid];
                    if port.closed || port.pos >= port.buffer.len() {
                        self.heap.alloc_special(table::EOF)
                    } else {
                        let remaining = std::str::from_utf8(&port.buffer[port.pos..]).unwrap_or("");
                        let mut reader = crate::reader::Reader::new(remaining);
                        match reader.read(&mut self.heap, &mut self.syms) {
                            Ok(val) => { self.ports[pid].pos += reader.position(); val }
                            _ => self.heap.alloc_special(table::EOF),
                        }
                    }
                }
            }
            131 => { // load
                let filename = self.extract_string(a1).unwrap_or_default();
                if let Ok(src) = std::fs::read_to_string(&filename) { self.eval_str(&src); }
                self.void_val
            }
            132 => { // read-char
                let pid = if a1 != Val::NIL && self.heap.tag(a1) == table::T_PORT {
                    self.heap.rib_car(a1).as_fixnum().unwrap_or(0) as usize
                } else { 0 };
                if pid < self.ports.len() && !self.ports[pid].closed && self.ports[pid].pos < self.ports[pid].buffer.len() {
                    let b = self.ports[pid].buffer[self.ports[pid].pos];
                    self.ports[pid].pos += 1;
                    self.heap.character(b as i64)
                } else { self.heap.alloc_special(table::EOF) }
            }
            133 => { // peek-char
                let pid = if a1 != Val::NIL && self.heap.tag(a1) == table::T_PORT {
                    self.heap.rib_car(a1).as_fixnum().unwrap_or(0) as usize
                } else { 0 };
                if pid < self.ports.len() && !self.ports[pid].closed && self.ports[pid].pos < self.ports[pid].buffer.len() {
                    self.heap.character(self.ports[pid].buffer[self.ports[pid].pos] as i64)
                } else { self.heap.alloc_special(table::EOF) }
            }
            134 => self.scheme_bool(self.heap.tag(a1) == table::T_PORT), // port?

            // ── Algebra extension ────────────
            200 => { // dot: (dot a b) → CAYLEY[a][b]
                let a = a1.as_fixnum().unwrap_or(0) as u8;
                let b = a2.as_fixnum().unwrap_or(0) as u8;
                Val::fixnum(table::dot(a, b) as i64)
            }
            201 => { // tau: (tau x) → type tag of x
                let tag = self.heap.tag(a1);
                Val::fixnum(tag as i64)
            }
            202 => { // type-valid?: (type-valid? op tag) → #t if not BOT
                let op = a1.as_fixnum().unwrap_or(0) as u8;
                let tag = a2.as_fixnum().unwrap_or(0) as u8;
                self.scheme_bool(table::dot(op, tag) != table::BOT)
            }
            203 => { // strict-mode
                self.strict = true;
                self.void_val
            }
            204 => { // permissive-mode
                self.strict = false;
                self.void_val
            }
            _ => Val::NIL,
        }
    }

    fn apply_proc_sync(&mut self, proc: Val, args: Val) -> Val {
        if self.heap.is_closure(proc) {
            let params = self.heap.rib_car(proc);
            let body_env = self.heap.rib_cdr(proc);
            let body = self.heap.car(body_env);
            let closed_env = self.heap.cdr(body_env);
            let env = self.extend_env(params, args, closed_env);
            self.eval(body, env)
        } else if proc.is_fixnum() {
            self.apply_builtin(proc, args)
        } else {
            Val::NIL
        }
    }

    fn equal(&self, a: Val, b: Val) -> bool {
        if a == b { return true; }
        if a.is_fixnum() || b.is_fixnum() { return false; }
        if a == Val::NIL || b == Val::NIL { return false; }
        let ta = self.heap.tag(a);
        let tb = self.heap.tag(b);
        if ta != tb { return false; }
        if ta == table::T_PAIR {
            self.equal(self.heap.car(a), self.heap.car(b))
                && self.equal(self.heap.cdr(a), self.heap.cdr(b))
        } else { false }
    }

    fn builtin_map(&mut self, proc: Val, lst: Val) -> Val {
        if !self.heap.is_pair(lst) { return Val::NIL; }
        let arg = self.heap.car(lst);
        let args = self.heap.cons(arg, Val::NIL);
        let val = self.apply_proc_sync(proc, args);
        let rest = self.builtin_map(proc, self.heap.cdr(lst));
        self.heap.cons(val, rest)
    }

    fn builtin_for_each(&mut self, proc: Val, mut lst: Val) {
        while self.heap.is_pair(lst) {
            let arg = self.heap.car(lst);
            let args = self.heap.cons(arg, Val::NIL);
            self.apply_proc_sync(proc, args);
            lst = self.heap.cdr(lst);
        }
    }

    fn make_string(&mut self, s: &str) -> Val {
        let mut chars = Val::NIL;
        for &b in s.as_bytes().iter().rev() {
            chars = self.heap.cons(Val::fixnum(b as i64), chars);
        }
        self.heap.string(chars, Val::fixnum(s.len() as i64))
    }

    fn extract_string(&self, str_rib: Val) -> Option<String> {
        if self.heap.tag(str_rib) != table::T_STR { return None; }
        let mut chars = self.heap.rib_car(str_rib);
        let mut s = String::new();
        while self.heap.is_pair(chars) {
            if let Some(cp) = self.heap.car(chars).as_fixnum() { s.push(cp as u8 as char); }
            chars = self.heap.cdr(chars);
        }
        Some(s)
    }

    pub fn display(&self, v: Val) {
        if v == Val::NIL { print!("()"); }
        else if v.is_fixnum() { print!("{}", v.as_fixnum().unwrap()); }
        else if self.heap.tag(v) == table::TRUE { print!("#t"); }
        else if self.heap.tag(v) == table::BOT { print!("#f"); }
        else {
            match self.heap.tag(v) {
                t if t == table::T_PAIR => {
                    print!("("); self.display(self.heap.car(v));
                    let mut r = self.heap.cdr(v);
                    while self.heap.is_pair(r) { print!(" "); self.display(self.heap.car(r)); r = self.heap.cdr(r); }
                    if r != Val::NIL { print!(" . "); self.display(r); }
                    print!(")");
                }
                t if t == table::T_SYM => {
                    if let Some(name) = self.syms.symbol_name(v) { print!("{name}"); }
                    else { print!("<sym>"); }
                }
                t if t == table::T_STR => {
                    if let Some(s) = self.extract_string(v) { print!("{s}"); }
                }
                t if t == table::T_CLS => print!("<procedure>"),
                t if t == table::T_CONT => print!("<continuation>"),
                _ => print!("<object>"),
            }
        }
    }

    /// Evaluate a string of Scheme source code.
    pub fn eval_str(&mut self, src: &str) -> Val {
        let exprs = crate::reader::read_all(src, &mut self.heap, &mut self.syms)
            .unwrap_or_default();
        let mut result = self.void_val;
        for &expr in exprs.iter() {
            result = self.eval(expr, Val::NIL);
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cps_arithmetic() {
        let mut ev = CpsEval::new();
        assert_eq!(ev.eval_str("(+ 3 4)"), Val::fixnum(7));
        assert_eq!(ev.eval_str("(* 6 7)"), Val::fixnum(42));
        assert_eq!(ev.eval_str("(+ (* 3 4) (* 5 6))"), Val::fixnum(42));
    }

    #[test]
    fn cps_if() {
        let mut ev = CpsEval::new();
        assert_eq!(ev.eval_str("(if #t 1 2)"), Val::fixnum(1));
        assert_eq!(ev.eval_str("(if #f 1 2)"), Val::fixnum(2));
    }

    #[test]
    fn cps_define_and_call() {
        let mut ev = CpsEval::new();
        ev.eval_str("(define (fact n) (if (= n 0) 1 (* n (fact (- n 1)))))");
        assert_eq!(ev.eval_str("(fact 10)"), Val::fixnum(3628800));
    }

    #[test]
    fn cps_fib() {
        let mut ev = CpsEval::new();
        ev.eval_str("(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))");
        assert_eq!(ev.eval_str("(fib 10)"), Val::fixnum(55));
    }

    #[test]
    fn cps_closures() {
        let mut ev = CpsEval::new();
        ev.eval_str("(define (make-adder n) (lambda (x) (+ x n)))");
        ev.eval_str("(define add10 (make-adder 10))");
        assert_eq!(ev.eval_str("(add10 32)"), Val::fixnum(42));
    }

    #[test]
    fn cps_tail_recursion() {
        let mut ev = CpsEval::new();
        ev.eval_str("(define (loop n) (if (= n 0) 0 (loop (- n 1))))");
        assert_eq!(ev.eval_str("(loop 100000)"), Val::fixnum(0));
    }

    #[test]
    fn cps_let() {
        let mut ev = CpsEval::new();
        assert_eq!(ev.eval_str("(let ((x 10) (y 20)) (+ x y))"), Val::fixnum(30));
    }

    #[test]
    fn cps_let_star() {
        let mut ev = CpsEval::new();
        assert_eq!(ev.eval_str("(let* ((x 1) (y (+ x 1))) y)"), Val::fixnum(2));
    }

    #[test]
    fn cps_named_let() {
        let mut ev = CpsEval::new();
        assert_eq!(
            ev.eval_str("(let loop ((n 10) (acc 0)) (if (= n 0) acc (loop (- n 1) (+ acc n))))"),
            Val::fixnum(55)
        );
    }

    #[test]
    fn cps_call_cc_escape() {
        let mut ev = CpsEval::new();
        assert_eq!(
            ev.eval_str("(call-with-current-continuation (lambda (k) (+ 1 (k 42))))"),
            Val::fixnum(42)
        );
    }

    #[test]
    fn cps_call_cc_no_escape() {
        let mut ev = CpsEval::new();
        assert_eq!(
            ev.eval_str("(call-with-current-continuation (lambda (k) 99))"),
            Val::fixnum(99)
        );
    }

    #[test]
    fn cps_call_cc_reentrant() {
        let mut ev = CpsEval::new();
        // Use call/cc to implement a simple coroutine-like pattern
        // within a single eval call
        ev.eval_str("(define saved #f)");
        let result = ev.eval_str("
            (let ((x (call-with-current-continuation (lambda (k) (set! saved k) 10))))
              (if (= x 10)
                  (saved 20)
                  x))
        ");
        assert_eq!(result, Val::fixnum(20));
    }

    // ── Algebra extension tests ────────────

    #[test]
    fn cps_algebra_dot() {
        let mut ev = CpsEval::new();
        assert_eq!(ev.eval_str("(dot CAR T_PAIR)"), Val::fixnum(table::T_PAIR as i64));
        assert_eq!(ev.eval_str("(dot CAR T_STR)"), Val::fixnum(table::BOT as i64));
    }

    #[test]
    fn cps_algebra_tau() {
        let mut ev = CpsEval::new();
        assert_eq!(ev.eval_str("(tau (cons 1 2))"), Val::fixnum(table::T_PAIR as i64));
        assert_eq!(ev.eval_str("(tau '())"), Val::fixnum(table::TOP as i64));
        assert_eq!(ev.eval_str("(tau \"hello\")"), Val::fixnum(table::T_STR as i64));
    }

    #[test]
    fn cps_algebra_type_valid() {
        let mut ev = CpsEval::new();
        let r1 = ev.eval_str("(type-valid? CAR T_PAIR)");
        assert!(ev.is_true(r1));
        let r2 = ev.eval_str("(type-valid? CAR T_STR)");
        assert!(!ev.is_true(r2));
        let r3 = ev.eval_str("(type-valid? CAR T_SYM)");
        assert!(!ev.is_true(r3));
    }

    #[test]
    fn cps_algebra_elements_bound() {
        let mut ev = CpsEval::new();
        assert_eq!(ev.eval_str("TOP"), Val::fixnum(0));
        assert_eq!(ev.eval_str("BOT"), Val::fixnum(1));
        assert_eq!(ev.eval_str("T_PAIR"), Val::fixnum(table::T_PAIR as i64));
        assert_eq!(ev.eval_str("Y"), Val::fixnum(table::Y as i64));
    }

    #[test]
    fn cps_algebra_user_dispatcher() {
        let mut ev = CpsEval::new();
        ev.eval_str("
            (define (type-name x)
              (let ((t (tau x)))
                (cond ((= t T_PAIR) 1)
                      ((= t T_STR) 2)
                      ((= t T_SYM) 3)
                      (else 0))))
        ");
        assert_eq!(ev.eval_str("(type-name (cons 1 2))"), Val::fixnum(1));
        assert_eq!(ev.eval_str("(type-name \"hello\")"), Val::fixnum(2));
        assert_eq!(ev.eval_str("(type-name 'foo)"), Val::fixnum(3));
    }

    #[test]
    fn cps_algebra_retraction() {
        let mut ev = CpsEval::new();
        assert_eq!(
            ev.eval_str("(dot E (dot Q CAR))"),
            ev.eval_str("CAR")
        );
        assert_eq!(
            ev.eval_str("(dot Q (dot E CAR))"),
            ev.eval_str("CAR")
        );
    }

    #[test]
    fn cps_algebra_y_fixed_point() {
        let mut ev = CpsEval::new();
        let yp = ev.eval_str("(dot Y RHO)");
        let ryp = ev.eval_str("(dot RHO (dot Y RHO))");
        assert_eq!(yp, ryp);
        let r = ev.eval_str("(> (dot Y RHO) 1)");
        assert!(ev.is_true(r));
    }

    #[test]
    fn cps_algebra_strict_mode() {
        let mut ev = CpsEval::new();
        assert!(!ev.strict);
        ev.eval_str("(strict-mode)");
        assert!(ev.strict);
        ev.eval_str("(permissive-mode)");
        assert!(!ev.strict);
    }

    #[test]
    fn cps_nqueens() {
        let mut ev = CpsEval::new();
        ev.eval_str("
            (define (abs-diff a b) (if (> a b) (- a b) (- b a)))
            (define (safe? queen dist placed)
              (if (null? placed) #t
                (let ((q (car placed)))
                  (cond ((= queen q) #f)
                        ((= (abs-diff queen q) dist) #f)
                        (else (safe? queen (+ dist 1) (cdr placed)))))))
            (define (nqueens-count n row placed)
              (if (= row n) 1
                (count-cols n 0 row placed)))
            (define (count-cols n col row placed)
              (if (= col n) 0
                (+ (if (safe? col 1 placed)
                     (nqueens-count n (+ row 1) (cons col placed))
                     0)
                   (count-cols n (+ col 1) row placed))))
            (define (nqueens n) (nqueens-count n 0 (list)))
        ");
        assert_eq!(ev.eval_str("(nqueens 6)"), Val::fixnum(4));
    }

    // ── char-ci / string-ci tests ────────────────────

    #[test]
    fn cps_char_ci_equal() {
        let mut ev = CpsEval::new();
        let r1 = ev.eval_str("(char-ci=? #\\a #\\A)");
        assert!(ev.is_true(r1));
        let r2 = ev.eval_str("(char-ci=? #\\a #\\b)");
        assert!(!ev.is_true(r2));
    }

    #[test]
    fn cps_string_ci_equal() {
        let mut ev = CpsEval::new();
        let r1 = ev.eval_str(r#"(string-ci=? "Hello" "hello")"#);
        assert!(ev.is_true(r1));
        let r2 = ev.eval_str(r#"(string-ci=? "ABC" "abd")"#);
        assert!(!ev.is_true(r2));
    }

    #[test]
    fn cps_string_ci_ordering() {
        let mut ev = CpsEval::new();
        let r1 = ev.eval_str(r#"(string-ci<? "abc" "ABD")"#);
        assert!(ev.is_true(r1));
        let r2 = ev.eval_str(r#"(string-ci>=? "ABC" "abc")"#);
        assert!(ev.is_true(r2));
    }
}
