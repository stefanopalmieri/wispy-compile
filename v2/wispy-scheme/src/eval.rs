//! Tree-walking evaluator for R4RS Scheme.
//!
//! Environments are rib lists: ((sym . val) . rest).
//! Closures are ribs: (params body . env) with tag T_CLS.
//! Tail calls use a trampoline to avoid stack overflow.

use crate::heap::Heap;
use crate::symbol::SymbolTable;
use crate::val::Val;
use crate::table;

/// Evaluation result: either a value or a tail-call thunk.
enum Trampoline {
    Done(Val),
    TailCall { proc: Val, args: Val },
}

/// The evaluator. Owns the heap, symbol table, and environment.
pub struct Eval {
    pub heap: Heap,
    pub syms: SymbolTable,
    /// Global environment: list of (symbol . value) pairs.
    pub globals: Val,
    /// The #t value (a rib with TRUE tag).
    pub true_val: Val,
    /// The #f value (a rib with BOT tag).
    pub false_val: Val,
    /// void
    pub void_val: Val,
    /// Continuation value slots for call/cc (escape continuations).
    cont_values: Vec<(usize, Val)>,
}

impl Eval {
    pub fn new() -> Self {
        let mut heap = Heap::new();
        let syms = SymbolTable::new();
        let true_val = heap.alloc_special(table::TRUE);
        let false_val = heap.alloc_special(table::BOT);
        let void_val = heap.alloc_special(table::VOID);

        let mut ev = Eval {
            heap,
            syms,
            globals: Val::NIL,
            true_val,
            false_val,
            void_val,
            cont_values: Vec::new(),
        };
        ev.register_builtins();
        ev
    }

    // ── Symbol interning (delegates to shared table) ─────────────

    pub fn intern(&mut self, name: &str) -> Val {
        self.syms.intern(name, &mut self.heap)
    }

    pub fn symbol_name(&self, sym: Val) -> Option<&str> {
        self.syms.symbol_name(sym)
    }

    fn sym_eq(&self, sym: Val, name: &str) -> bool {
        self.syms.sym_eq(sym, name)
    }

    // ── String helpers ───────────────────────────────────────────

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
            if let Some(cp) = self.heap.car(chars).as_fixnum() {
                s.push(cp as u8 as char);
            }
            chars = self.heap.cdr(chars);
        }
        Some(s)
    }

    // ── Environment ──────────────────────────────────────────────

    /// Look up a variable in an environment.
    /// Symbols are interned, so comparison is pointer equality.
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

    /// Set a variable in the global environment.
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
        // New binding
        let binding = self.heap.cons(sym, val);
        self.globals = self.heap.cons(binding, self.globals);
    }

    /// Extend an environment with new bindings.
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

        // Rest parameter: (lambda (a b . rest) ...)
        if self.heap.is_symbol(p) {
            let binding = self.heap.cons(p, a);
            new_env = self.heap.cons(binding, new_env);
        }

        new_env
    }

    // ── Eval ─────────────────────────────────────────────────────

    /// Evaluate an expression in an environment.
    pub fn eval(&mut self, expr: Val, env: Val) -> Val {
        let mut expr = expr;
        let mut env = env;

        loop {
            match self.eval_inner(expr, env) {
                Trampoline::Done(v) => return v,
                Trampoline::TailCall { proc, args } => {
                    // Trampoline: unpack closure, extend env, loop
                    if self.heap.is_closure(proc) {
                        let params = self.heap.rib_car(proc);
                        let body_env = self.heap.rib_cdr(proc);
                        let body = self.heap.car(body_env);
                        let closed_env = self.heap.cdr(body_env);
                        env = self.extend_env(params, args, closed_env);
                        expr = body;
                        // continue loop (tail call)
                    } else {
                        // Built-in — shouldn't produce tail calls normally
                        return self.apply(proc, args);
                    }
                }
            }
        }
    }

    fn eval_inner(&mut self, expr: Val, env: Val) -> Trampoline {
        // Fixnum: self-evaluating
        if expr.is_fixnum() {
            return Trampoline::Done(expr);
        }

        // Nil: self-evaluating
        if expr == Val::NIL {
            return Trampoline::Done(Val::NIL);
        }

        // Non-rib, non-fixnum shouldn't happen
        if !expr.is_rib() {
            return Trampoline::Done(Val::NIL);
        }

        let tag = self.heap.tag(expr);

        // Symbol: variable lookup
        if tag == table::T_SYM {
            return Trampoline::Done(
                self.lookup(expr, env).unwrap_or(Val::NIL)
            );
        }

        // String, char, vector, etc.: self-evaluating
        if tag != table::T_PAIR {
            return Trampoline::Done(expr);
        }

        // Pair: either special form or procedure call
        let head = self.heap.car(expr);
        let rest = self.heap.cdr(expr);

        // Check for special forms (head is a symbol)
        if self.heap.is_symbol(head) {
            if self.sym_eq(head, "quote") {
                return Trampoline::Done(self.heap.car(rest));
            }

            if self.sym_eq(head, "if") {
                let test = self.heap.car(rest);
                let rest2 = self.heap.cdr(rest);
                let consequent = self.heap.car(rest2);
                let alternate = self.heap.car(self.heap.cdr(rest2));

                let test_val = self.eval(test, env);
                if self.is_true(test_val) {
                    return self.eval_inner(consequent, env); // tail position
                } else {
                    return self.eval_inner(alternate, env); // tail position
                }
            }

            if self.sym_eq(head, "define") {
                let target = self.heap.car(rest);
                if self.heap.is_symbol(target) {
                    // (define x expr)
                    let val = self.eval(self.heap.car(self.heap.cdr(rest)), env);
                    self.define_global(target, val);
                    return Trampoline::Done(self.void_val);
                } else if self.heap.is_pair(target) {
                    // (define (f args...) body...) → (define f (lambda (args...) body...))
                    let name = self.heap.car(target);
                    let params = self.heap.cdr(target);
                    let body_exprs = self.heap.cdr(rest);
                    let body = if self.heap.cdr(body_exprs) == Val::NIL {
                        self.heap.car(body_exprs)
                    } else {
                        let begin_sym = self.intern("begin");
                        self.heap.cons(begin_sym, body_exprs)
                    };
                    let body_env = self.heap.cons(body, env);
                    let closure = self.heap.closure(params, body_env);
                    self.define_global(name, closure);
                    return Trampoline::Done(self.void_val);
                }
            }

            if self.sym_eq(head, "lambda") {
                let params = self.heap.car(rest);
                let body_exprs = self.heap.cdr(rest);
                // Multi-body: wrap in (begin ...) if more than one
                let body = if self.heap.cdr(body_exprs) == Val::NIL {
                    self.heap.car(body_exprs)
                } else {
                    let begin_sym = self.intern("begin");
                    self.heap.cons(begin_sym, body_exprs)
                };
                let body_env = self.heap.cons(body, env);
                let closure = self.heap.closure(params, body_env);
                return Trampoline::Done(closure);
            }

            if self.sym_eq(head, "set!") {
                let sym = self.heap.car(rest);
                let val = self.eval(self.heap.car(self.heap.cdr(rest)), env);
                // Find and update binding
                self.set_variable(sym, val, env);
                return Trampoline::Done(self.void_val);
            }

            if self.sym_eq(head, "begin") {
                return self.eval_begin(rest, env);
            }

            if self.sym_eq(head, "cond") {
                return self.eval_cond(rest, env);
            }

            if self.sym_eq(head, "and") {
                return self.eval_and(rest, env);
            }

            if self.sym_eq(head, "or") {
                return self.eval_or(rest, env);
            }

            if self.sym_eq(head, "let") {
                return self.eval_let(rest, env);
            }

            if self.sym_eq(head, "letrec") {
                return self.eval_letrec(rest, env);
            }

            if self.sym_eq(head, "let*") {
                return self.eval_let_star(rest, env);
            }

            if self.sym_eq(head, "case") {
                return self.eval_case(rest, env);
            }

            if self.sym_eq(head, "do") {
                return self.eval_do(rest, env);
            }

            if self.sym_eq(head, "delay") {
                let expr = self.heap.car(rest);
                let promise = self.make_promise(expr, env);
                return Trampoline::Done(promise);
            }

            if self.sym_eq(head, "quasiquote") {
                let template = self.heap.car(rest);
                let result = self.expand_quasiquote(template, env);
                return Trampoline::Done(result);
            }
        }

        // Procedure call: (proc arg1 arg2 ...)
        let proc = self.eval(head, env);

        // call/cc needs special handling
        if proc.is_fixnum() && proc.as_fixnum() == Some(70) {
            let arg = self.eval(self.heap.car(rest), env);
            return Trampoline::Done(self.call_cc(arg, env));
        }

        let args = self.eval_list(rest, env);

        // Tail call optimization for closures
        if self.heap.is_closure(proc) {
            Trampoline::TailCall { proc, args }
        } else {
            Trampoline::Done(self.apply(proc, args))
        }
    }

    /// Evaluate a list of expressions, returning a list of values.
    fn eval_list(&mut self, mut exprs: Val, env: Val) -> Val {
        let mut results = Vec::new();
        while self.heap.is_pair(exprs) {
            let val = self.eval(self.heap.car(exprs), env);
            results.push(val);
            exprs = self.heap.cdr(exprs);
        }
        self.heap.list(&results)
    }

    fn eval_begin(&mut self, mut body: Val, env: Val) -> Trampoline {
        if body == Val::NIL {
            return Trampoline::Done(self.void_val);
        }
        while self.heap.is_pair(self.heap.cdr(body)) {
            self.eval(self.heap.car(body), env);
            body = self.heap.cdr(body);
        }
        // Last expression in tail position
        self.eval_inner(self.heap.car(body), env)
    }

    fn eval_cond(&mut self, mut clauses: Val, env: Val) -> Trampoline {
        while self.heap.is_pair(clauses) {
            let clause = self.heap.car(clauses);
            let test_expr = self.heap.car(clause);
            let body = self.heap.cdr(clause);

            // Check for (else ...)
            if self.heap.is_symbol(test_expr) && self.sym_eq(test_expr, "else") {
                return self.eval_begin(body, env);
            }

            let test_val = self.eval(test_expr, env);
            if self.is_true(test_val) {
                if body == Val::NIL {
                    return Trampoline::Done(test_val);
                }
                return self.eval_begin(body, env);
            }

            clauses = self.heap.cdr(clauses);
        }
        Trampoline::Done(self.void_val)
    }

    fn eval_and(&mut self, mut exprs: Val, env: Val) -> Trampoline {
        if exprs == Val::NIL {
            return Trampoline::Done(self.true_val);
        }
        let mut val = self.true_val;
        while self.heap.is_pair(exprs) {
            val = self.eval(self.heap.car(exprs), env);
            if !self.is_true(val) {
                return Trampoline::Done(val);
            }
            exprs = self.heap.cdr(exprs);
        }
        Trampoline::Done(val)
    }

    fn eval_or(&mut self, mut exprs: Val, env: Val) -> Trampoline {
        if exprs == Val::NIL {
            return Trampoline::Done(self.false_val);
        }
        while self.heap.is_pair(exprs) {
            let val = self.eval(self.heap.car(exprs), env);
            if self.is_true(val) {
                return Trampoline::Done(val);
            }
            exprs = self.heap.cdr(exprs);
        }
        Trampoline::Done(self.false_val)
    }

    fn eval_let(&mut self, rest: Val, env: Val) -> Trampoline {
        let first = self.heap.car(rest);

        // Named let: (let name ((var init) ...) body ...)
        if self.heap.is_symbol(first) {
            let name = first;
            let bindings = self.heap.car(self.heap.cdr(rest));
            let body = self.heap.cdr(self.heap.cdr(rest));

            // Collect params and init values
            let mut params = Vec::new();
            let mut inits = Vec::new();
            let mut b = bindings;
            while self.heap.is_pair(b) {
                let binding = self.heap.car(b);
                params.push(self.heap.car(binding));
                let init_expr = self.heap.car(self.heap.cdr(binding));
                inits.push(self.eval(init_expr, env));
                b = self.heap.cdr(b);
            }

            // Build the lambda
            let param_list = self.heap.list(&params);
            let body_expr = if self.heap.cdr(body) == Val::NIL {
                self.heap.car(body)
            } else {
                let begin_sym = self.intern("begin");
                self.heap.cons(begin_sym, body)
            };
            let body_env_rib = self.heap.cons(body_expr, env);
            let closure = self.heap.closure(param_list, body_env_rib);

            // Bind name to the closure in a recursive env
            let binding = self.heap.cons(name, closure);
            let rec_env = self.heap.cons(binding, env);
            // Update the closure's env to include itself
            let new_body_env = self.heap.cons(body_expr, rec_env);
            self.heap.set_cdr_raw(closure, new_body_env);

            // Apply with init values
            let args = self.heap.list(&inits);
            return Trampoline::TailCall { proc: closure, args };
        }

        // Regular let: (let ((var init) ...) body ...)
        let bindings = first;
        let body = self.heap.cdr(rest);

        let mut new_env = env;
        let mut b = bindings;
        while self.heap.is_pair(b) {
            let binding = self.heap.car(b);
            let sym = self.heap.car(binding);
            let init_expr = self.heap.car(self.heap.cdr(binding));
            let val = self.eval(init_expr, env); // eval in outer env for let
            let pair = self.heap.cons(sym, val);
            new_env = self.heap.cons(pair, new_env);
            b = self.heap.cdr(b);
        }

        self.eval_begin(body, new_env)
    }

    fn eval_letrec(&mut self, rest: Val, env: Val) -> Trampoline {
        let bindings = self.heap.car(rest);
        let body = self.heap.cdr(rest);

        // First pass: bind all names to NIL
        let mut new_env = env;
        let mut b = bindings;
        while self.heap.is_pair(b) {
            let binding = self.heap.car(b);
            let sym = self.heap.car(binding);
            let pair = self.heap.cons(sym, Val::NIL);
            new_env = self.heap.cons(pair, new_env);
            b = self.heap.cdr(b);
        }

        // Second pass: evaluate inits in the new env and set
        b = bindings;
        let mut e = new_env;
        while self.heap.is_pair(b) {
            let binding = self.heap.car(b);
            let init_expr = self.heap.car(self.heap.cdr(binding));
            let val = self.eval(init_expr, new_env);
            // Update the binding in new_env
            self.heap.set_cdr(self.heap.car(e), val);
            b = self.heap.cdr(b);
            e = self.heap.cdr(e);
        }

        self.eval_begin(body, new_env)
    }

    fn eval_let_star(&mut self, rest: Val, env: Val) -> Trampoline {
        let bindings = self.heap.car(rest);
        let body = self.heap.cdr(rest);

        let mut new_env = env;
        let mut b = bindings;
        while self.heap.is_pair(b) {
            let binding = self.heap.car(b);
            let sym = self.heap.car(binding);
            let init_expr = self.heap.car(self.heap.cdr(binding));
            let val = self.eval(init_expr, new_env); // sequential: use growing env
            let pair = self.heap.cons(sym, val);
            new_env = self.heap.cons(pair, new_env);
            b = self.heap.cdr(b);
        }

        self.eval_begin(body, new_env)
    }

    fn eval_case(&mut self, rest: Val, env: Val) -> Trampoline {
        let key_expr = self.heap.car(rest);
        let key = self.eval(key_expr, env);
        let mut clauses = self.heap.cdr(rest);

        while self.heap.is_pair(clauses) {
            let clause = self.heap.car(clauses);
            let datums = self.heap.car(clause);
            let body = self.heap.cdr(clause);

            // (else ...) clause
            if self.heap.is_symbol(datums) && self.sym_eq(datums, "else") {
                return self.eval_begin(body, env);
            }

            // Check if key is eqv? to any datum in the list
            let mut d = datums;
            while self.heap.is_pair(d) {
                let datum = self.heap.car(d);
                if key == datum || (key.is_fixnum() && datum.is_fixnum()
                    && key.as_fixnum() == datum.as_fixnum())
                {
                    return self.eval_begin(body, env);
                }
                d = self.heap.cdr(d);
            }

            clauses = self.heap.cdr(clauses);
        }
        Trampoline::Done(self.void_val)
    }

    fn eval_do(&mut self, rest: Val, env: Val) -> Trampoline {
        // (do ((var init step) ...) (test expr ...) command ...)
        let var_specs = self.heap.car(rest);
        let test_clause = self.heap.car(self.heap.cdr(rest));
        let commands = self.heap.cdr(self.heap.cdr(rest));

        // Initialize variables
        let mut new_env = env;
        let mut specs = Vec::new();
        let mut vs = var_specs;
        while self.heap.is_pair(vs) {
            let spec = self.heap.car(vs);
            let var = self.heap.car(spec);
            let init_expr = self.heap.car(self.heap.cdr(spec));
            let step = self.heap.cdr(self.heap.cdr(spec));
            let step_expr = if self.heap.is_pair(step) {
                Some(self.heap.car(step))
            } else {
                None
            };

            let init_val = self.eval(init_expr, env);
            let binding = self.heap.cons(var, init_val);
            new_env = self.heap.cons(binding, new_env);
            specs.push((var, step_expr));
            vs = self.heap.cdr(vs);
        }

        let test_expr = self.heap.car(test_clause);
        let result_exprs = self.heap.cdr(test_clause);

        loop {
            // Test
            let test_val = self.eval(test_expr, new_env);
            if self.is_true(test_val) {
                // Evaluate result expressions
                if result_exprs == Val::NIL {
                    return Trampoline::Done(self.void_val);
                }
                return self.eval_begin(result_exprs, new_env);
            }

            // Execute commands
            let mut cmd = commands;
            while self.heap.is_pair(cmd) {
                self.eval(self.heap.car(cmd), new_env);
                cmd = self.heap.cdr(cmd);
            }

            // Step variables
            let mut new_vals = Vec::new();
            for (_, step_expr) in &specs {
                if let Some(expr) = step_expr {
                    new_vals.push(self.eval(*expr, new_env));
                } else {
                    new_vals.push(Val::NIL); // placeholder, won't be used
                }
            }

            // Update bindings
            let mut e = new_env;
            for (i, (_, step_expr)) in specs.iter().enumerate().rev() {
                // Find the binding for this var (it's at the head of new_env
                // since we pushed them in order)
                if step_expr.is_some() {
                    // Walk to the right binding
                    let mut walk = new_env;
                    for _ in 0..(specs.len() - 1 - i) {
                        walk = self.heap.cdr(walk);
                    }
                    self.heap.set_cdr(self.heap.car(walk), new_vals[i]);
                }
            }
            let _ = e;
        }
    }

    // ── Promises (delay/force) ───────────────────────────────────

    fn make_promise(&mut self, expr: Val, env: Val) -> Val {
        // Promise = rib (expr . env, result, T_CONT)
        // We reuse T_CONT tag with a convention:
        // car = (expr . env), cdr = NIL (unforced) or (value) (forced)
        let expr_env = self.heap.cons(expr, env);
        self.heap.alloc_rib(expr_env, Val::NIL, table::T_CONT)
    }

    fn force_promise(&mut self, promise: Val) -> Val {
        if self.heap.tag(promise) != table::T_CONT {
            return promise; // not a promise, return as-is
        }
        let cached = self.heap.rib_cdr(promise);
        if self.heap.is_pair(cached) {
            // Already forced
            return self.heap.car(cached);
        }
        // Force it
        let expr_env = self.heap.rib_car(promise);
        let expr = self.heap.car(expr_env);
        let env = self.heap.cdr(expr_env);
        let result = self.eval(expr, env);
        // Cache the result
        let cached = self.heap.cons(result, Val::NIL);
        self.heap.set_cdr_raw(promise, cached);
        result
    }

    // ── Quasiquote ───────────────────────────────────────────────

    fn expand_quasiquote(&mut self, template: Val, env: Val) -> Val {
        if !self.heap.is_pair(template) {
            return template;
        }

        let head = self.heap.car(template);
        if self.heap.is_symbol(head) && self.sym_eq(head, "unquote") {
            let expr = self.heap.car(self.heap.cdr(template));
            return self.eval(expr, env);
        }

        // Check for (unquote-splicing ...) in car position
        if self.heap.is_pair(head) {
            let head_head = self.heap.car(head);
            if self.heap.is_symbol(head_head) && self.sym_eq(head_head, "unquote-splicing") {
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

    // ── call/cc ──────────────────────────────────────────────────

    fn call_cc(&mut self, proc: Val, env: Val) -> Val {
        // We implement call/cc using Rust's panic/catch mechanism
        // as a simple escape continuation.
        //
        // A continuation is a closure that, when called, returns
        // its argument as the result of the call/cc expression.
        //
        // For a full implementation, we'd need CPS transform.
        // This gives us escape continuations (sufficient for most R4RS uses).
        use std::panic::{catch_unwind, AssertUnwindSafe};

        // Create a unique tag for this continuation
        let cont_id = self.heap.len();

        // Create a continuation procedure (stored as a builtin with special id)
        // We use a negative fixnum as the continuation marker
        let cont = Val::fixnum(-(cont_id as i64));

        // Store the continuation value slot
        self.cont_values.push((cont_id, Val::NIL));

        let args = self.heap.cons(cont, Val::NIL);

        // Try to apply proc to the continuation
        let result = catch_unwind(AssertUnwindSafe(|| {
            self.apply(proc, args)
        }));

        match result {
            Ok(v) => v,
            Err(payload) => {
                // Check if it was our continuation
                if let Some(&(id, val)) = self.cont_values.last() {
                    if id == cont_id {
                        self.cont_values.pop();
                        return val;
                    }
                }
                // Not our continuation, re-panic
                std::panic::resume_unwind(payload);
            }
        }
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

    // ── Apply ────────────────────────────────────────────────────

    fn apply(&mut self, proc: Val, args: Val) -> Val {
        if self.heap.is_closure(proc) {
            let params = self.heap.rib_car(proc);
            let body_env = self.heap.rib_cdr(proc);
            let body = self.heap.car(body_env);
            let closed_env = self.heap.cdr(body_env);
            let env = self.extend_env(params, args, closed_env);
            self.eval(body, env)
        } else if proc.is_fixnum() {
            // Built-in function (represented as fixnum index)
            self.apply_builtin(proc, args)
        } else {
            Val::NIL // error: not a procedure
        }
    }

    // ── Truthiness ───────────────────────────────────────────────

    pub fn is_true(&self, v: Val) -> bool {
        if v == Val::NIL { return false; }
        if v.is_rib() && self.heap.tag(v) == table::BOT { return false; }
        true
    }

    pub fn scheme_bool(&mut self, b: bool) -> Val {
        if b { self.true_val } else { self.false_val }
    }

    // ── Builtins ─────────────────────────────────────────────────

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
            ("gcd", 43),
            ("map", 44), ("for-each", 45),
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
            ("force", 71),
            ("/", 72), ("lcm", 73),
            ("string=?", 74), ("string<?", 75),
            ("substring", 76), ("string->list", 77), ("list->string", 78),
            ("vector->list", 79), ("list->vector", 80),
            ("char=?", 81), ("char<?", 82),
            ("char-alphabetic?", 83), ("char-numeric?", 84),
            ("char-whitespace?", 85), ("char-upper-case?", 86),
            ("char-lower-case?", 87), ("char-upcase", 88), ("char-downcase", 89),
            ("string-set!", 90),
            ("integer?", 91), ("exact?", 92), ("inexact?", 93),
            ("expt", 94),
            ("string>?", 95), ("string<=?", 96), ("string>=?", 97),
            ("char>?", 98), ("char<=?", 99), ("char>=?", 100),
            ("eof-object?", 101),
            ("write-char", 102),
            ("error", 103),
            // ── Algebra extension (wispy algebra) ────────────
            ("dot", 200),       // (dot a b) → CAYLEY[a][b]
            ("tau", 201),       // (tau x) → type tag of x
            ("type-valid?", 202), // (type-valid? op tag) → #t if not BOT
        ];

        for (name, id) in builtins {
            let sym = self.intern(name);
            self.define_global(sym, Val::fixnum(id));
        }

        // Algebra element constants — the programmer can reach into the table
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
            let sym = self.intern(name);
            self.define_global(sym, Val::fixnum(elem as i64));
        }
    }

    fn apply_builtin(&mut self, id: Val, args: Val) -> Val {
        let id = id.as_fixnum().unwrap();

        // Negative id = escape continuation
        if id < 0 {
            let cont_id = (-id) as usize;
            let val = self.heap.car(args);
            // Store the value and panic to unwind to the call/cc site
            for entry in &mut self.cont_values {
                if entry.0 == cont_id {
                    entry.1 = val;
                    break;
                }
            }
            panic!("continuation-escape-{}", cont_id);
        }

        // Helper to extract args
        let a1 = self.heap.car(args);
        let a2 = self.heap.car(self.heap.cdr(args));

        match id {
            // Arithmetic
            0 => { // +
                let mut sum = 0i64;
                let mut a = args;
                while self.heap.is_pair(a) {
                    sum += self.heap.car(a).as_fixnum().unwrap_or(0);
                    a = self.heap.cdr(a);
                }
                Val::fixnum(sum)
            }
            1 => { // -
                if self.heap.cdr(args) == Val::NIL {
                    // Unary minus
                    Val::fixnum(-a1.as_fixnum().unwrap_or(0))
                } else {
                    let mut result = a1.as_fixnum().unwrap_or(0);
                    let mut a = self.heap.cdr(args);
                    while self.heap.is_pair(a) {
                        result -= self.heap.car(a).as_fixnum().unwrap_or(0);
                        a = self.heap.cdr(a);
                    }
                    Val::fixnum(result)
                }
            }
            2 => { // *
                let mut prod = 1i64;
                let mut a = args;
                while self.heap.is_pair(a) {
                    prod *= self.heap.car(a).as_fixnum().unwrap_or(0);
                    a = self.heap.cdr(a);
                }
                Val::fixnum(prod)
            }
            3 => Val::fixnum(a1.as_fixnum().unwrap_or(0) / a2.as_fixnum().unwrap_or(1)), // quotient
            4 => Val::fixnum(a1.as_fixnum().unwrap_or(0) % a2.as_fixnum().unwrap_or(1)), // remainder
            5 => { // modulo
                let (a, b) = (a1.as_fixnum().unwrap_or(0), a2.as_fixnum().unwrap_or(1));
                Val::fixnum(((a % b) + b) % b)
            }

            // Comparison
            6 => self.scheme_bool(a1.as_fixnum() == a2.as_fixnum()),  // =
            7 => self.scheme_bool(a1.as_fixnum() < a2.as_fixnum()),   // <
            8 => self.scheme_bool(a1.as_fixnum() > a2.as_fixnum()),   // >
            9 => self.scheme_bool(a1.as_fixnum() <= a2.as_fixnum()),  // <=
            10 => self.scheme_bool(a1.as_fixnum() >= a2.as_fixnum()), // >=

            // Pairs
            11 => self.heap.cons(a1, a2),           // cons
            12 => self.heap.car(a1),                 // car
            13 => self.heap.cdr(a1),                 // cdr
            14 => { self.heap.set_car(a1, a2); self.void_val } // set-car!
            15 => { self.heap.set_cdr(a1, a2); self.void_val } // set-cdr!

            // Type predicates
            16 => self.scheme_bool(a1 == Val::NIL),                   // null?
            17 => self.scheme_bool(self.heap.is_pair(a1)),             // pair?
            18 => self.scheme_bool(a1.is_fixnum()),                    // number?
            19 => self.scheme_bool(self.heap.is_symbol(a1)),           // symbol?
            20 => self.scheme_bool(self.heap.is_string(a1)),           // string?
            21 => self.scheme_bool(self.heap.is_vector(a1)),           // vector?
            22 => self.scheme_bool(self.heap.tag(a1) == table::T_CHAR), // char?
            23 => self.scheme_bool(self.heap.is_closure(a1) || a1.is_fixnum()), // procedure?
            24 => self.scheme_bool(a1 == self.true_val || a1 == self.false_val), // boolean?

            // Boolean
            25 => self.scheme_bool(!self.is_true(a1)), // not
            26 => self.scheme_bool(a1 == a2),          // eq?
            27 => self.scheme_bool(self.equal(a1, a2)), // equal?
            28 => self.scheme_bool(a1 == a2),          // eqv?

            // List operations
            29 => args, // list — args is already a list!
            30 => Val::fixnum(self.heap.length(a1) as i64), // length
            31 => { // append
                if self.heap.cdr(args) == Val::NIL { return a1; }
                self.append(a1, a2)
            }

            // I/O
            32 => { self.display(a1); self.void_val }  // display
            33 => { println!(); self.void_val }         // newline
            34 => { self.write(a1); self.void_val }     // write

            // Number predicates
            35 => self.scheme_bool(a1.as_fixnum() == Some(0)),  // zero?
            36 => self.scheme_bool(a1.as_fixnum().map_or(false, |n| n > 0)), // positive?
            37 => self.scheme_bool(a1.as_fixnum().map_or(false, |n| n < 0)), // negative?
            38 => self.scheme_bool(a1.as_fixnum().map_or(false, |n| n % 2 == 0)), // even?
            39 => self.scheme_bool(a1.as_fixnum().map_or(false, |n| n % 2 != 0)), // odd?

            40 => Val::fixnum(a1.as_fixnum().unwrap_or(0).abs()), // abs
            41 => Val::fixnum(a1.as_fixnum().unwrap_or(0).max(a2.as_fixnum().unwrap_or(0))), // max
            42 => Val::fixnum(a1.as_fixnum().unwrap_or(0).min(a2.as_fixnum().unwrap_or(0))), // min
            43 => { // gcd
                let (mut a, mut b) = (a1.as_fixnum().unwrap_or(0).abs(),
                                      a2.as_fixnum().unwrap_or(0).abs());
                while b != 0 { let t = b; b = a % b; a = t; }
                Val::fixnum(a)
            }

            // Higher-order
            44 => self.builtin_map(a1, a2),       // map
            45 => { self.builtin_for_each(a1, a2); self.void_val } // for-each
            46 => { // apply
                // (apply proc arg1 ... args)
                // Last argument must be a list
                self.apply(a1, a2)
            }

            // Char
            47 => { // char->integer
                let cp = self.heap.rib_car(a1).as_fixnum().unwrap_or(0);
                Val::fixnum(cp)
            }
            48 => self.heap.character(a1.as_fixnum().unwrap_or(0)), // integer->char

            // Number/string conversion
            49 => { // number->string
                let n = a1.as_fixnum().unwrap_or(0);
                let s = format!("{n}");
                self.make_string(&s)
            }
            50 => { // string->number
                if let Some(s) = self.extract_string(a1) {
                    if let Ok(n) = s.parse::<i64>() {
                        Val::fixnum(n)
                    } else {
                        self.false_val
                    }
                } else {
                    self.false_val
                }
            }

            // String operations
            51 => { // string-length
                self.heap.rib_cdr(a1) // cdr of string rib is length
            }
            52 => { // string-ref
                let idx = a2.as_fixnum().unwrap_or(0);
                let mut chars = self.heap.rib_car(a1);
                for _ in 0..idx {
                    chars = self.heap.cdr(chars);
                }
                let cp = self.heap.car(chars).as_fixnum().unwrap_or(0);
                self.heap.character(cp)
            }
            53 => { // string-append
                let s1 = self.extract_string(a1).unwrap_or_default();
                let s2 = self.extract_string(a2).unwrap_or_default();
                self.make_string(&format!("{s1}{s2}"))
            }

            // Vector operations
            54 => self.heap.rib_cdr(a1), // vector-length
            55 => { // vector-ref
                let idx = a2.as_fixnum().unwrap_or(0);
                let mut elems = self.heap.rib_car(a1);
                for _ in 0..idx {
                    elems = self.heap.cdr(elems);
                }
                self.heap.car(elems)
            }
            56 => { // vector-set!
                let idx = a2.as_fixnum().unwrap_or(0);
                let a3 = self.heap.car(self.heap.cdr(self.heap.cdr(args)));
                let mut elems = self.heap.rib_car(a1);
                for _ in 0..idx {
                    elems = self.heap.cdr(elems);
                }
                self.heap.set_car(elems, a3);
                self.void_val
            }
            57 => { // make-vector
                let len = a1.as_fixnum().unwrap_or(0);
                let fill = a2;
                let mut elems = Val::NIL;
                for _ in 0..len {
                    elems = self.heap.cons(fill, elems);
                }
                self.heap.vector(elems, Val::fixnum(len))
            }
            58 => { // make-string
                let len = a1.as_fixnum().unwrap_or(0);
                let fill = if a2.is_fixnum() { a2.as_fixnum().unwrap_or(b' ' as i64) }
                           else { self.heap.rib_car(a2).as_fixnum().unwrap_or(b' ' as i64) };
                let mut chars = Val::NIL;
                for _ in 0..len {
                    chars = self.heap.cons(Val::fixnum(fill), chars);
                }
                self.heap.string(chars, Val::fixnum(len))
            }

            // Symbol/string conversion
            59 => { // symbol->string
                self.heap.rib_car(a1) // car of symbol is its name (string rib)
            }
            60 => { // string->symbol
                if let Some(name) = self.extract_string(a1) {
                    self.intern(&name)
                } else {
                    Val::NIL
                }
            }

            61 => { // reverse
                let mut result = Val::NIL;
                let mut lst = a1;
                while self.heap.is_pair(lst) {
                    result = self.heap.cons(self.heap.car(lst), result);
                    lst = self.heap.cdr(lst);
                }
                result
            }

            // List access
            62 => { // list-ref
                let idx = a2.as_fixnum().unwrap_or(0);
                let mut lst = a1;
                for _ in 0..idx { lst = self.heap.cdr(lst); }
                self.heap.car(lst)
            }
            63 => { // list-tail
                let idx = a2.as_fixnum().unwrap_or(0);
                let mut lst = a1;
                for _ in 0..idx { lst = self.heap.cdr(lst); }
                lst
            }

            // Association lists
            64 => { // memq
                let mut lst = a2;
                while self.heap.is_pair(lst) {
                    if self.heap.car(lst) == a1 { return lst; }
                    lst = self.heap.cdr(lst);
                }
                self.false_val
            }
            65 => self.apply_builtin(Val::fixnum(64), args), // memv = memq for fixnums
            66 => { // member (uses equal?)
                let mut lst = a2;
                while self.heap.is_pair(lst) {
                    if self.equal(self.heap.car(lst), a1) { return lst; }
                    lst = self.heap.cdr(lst);
                }
                self.false_val
            }
            67 => { // assq
                let mut lst = a2;
                while self.heap.is_pair(lst) {
                    let pair = self.heap.car(lst);
                    if self.heap.is_pair(pair) && self.heap.car(pair) == a1 {
                        return pair;
                    }
                    lst = self.heap.cdr(lst);
                }
                self.false_val
            }
            68 => self.apply_builtin(Val::fixnum(67), args), // assv = assq for fixnums
            69 => { // assoc (uses equal?)
                let mut lst = a2;
                while self.heap.is_pair(lst) {
                    let pair = self.heap.car(lst);
                    if self.heap.is_pair(pair) && self.equal(self.heap.car(pair), a1) {
                        return pair;
                    }
                    lst = self.heap.cdr(lst);
                }
                self.false_val
            }

            // call/cc
            70 => { // call-with-current-continuation
                let env = Val::NIL; // globals
                self.call_cc(a1, env)
            }

            // force
            71 => self.force_promise(a1),

            // Division
            72 => { // /
                let b = a2.as_fixnum().unwrap_or(1);
                if b == 0 { Val::NIL } // division by zero
                else { Val::fixnum(a1.as_fixnum().unwrap_or(0) / b) }
            }
            73 => { // lcm
                let (a, b) = (a1.as_fixnum().unwrap_or(0).abs(),
                              a2.as_fixnum().unwrap_or(0).abs());
                if a == 0 || b == 0 { Val::fixnum(0) }
                else {
                    let mut ga = a; let mut gb = b;
                    while gb != 0 { let t = gb; gb = ga % gb; ga = t; }
                    Val::fixnum(a / ga * b)
                }
            }

            // String comparisons
            74 => { // string=?
                let sa = self.extract_string(a1).unwrap_or_default();
                let sb = self.extract_string(a2).unwrap_or_default();
                self.scheme_bool(sa == sb)
            }
            75 => { // string<?
                let sa = self.extract_string(a1).unwrap_or_default();
                let sb = self.extract_string(a2).unwrap_or_default();
                self.scheme_bool(sa < sb)
            }
            76 => { // substring
                let s = self.extract_string(a1).unwrap_or_default();
                let start = a2.as_fixnum().unwrap_or(0) as usize;
                let a3 = self.heap.car(self.heap.cdr(self.heap.cdr(args)));
                let end = a3.as_fixnum().unwrap_or(s.len() as i64) as usize;
                self.make_string(&s[start..end])
            }
            77 => { // string->list
                let s = self.extract_string(a1).unwrap_or_default();
                let chars: Vec<Val> = s.bytes().map(|b| Val::fixnum(b as i64)).collect();
                // Wrap each in a char rib
                let char_ribs: Vec<Val> = chars.iter().map(|&cp| {
                    self.heap.character(cp.as_fixnum().unwrap_or(0))
                }).collect();
                self.heap.list(&char_ribs)
            }
            78 => { // list->string
                let mut result = String::new();
                let mut lst = a1;
                while self.heap.is_pair(lst) {
                    let ch = self.heap.car(lst);
                    let cp = self.heap.rib_car(ch).as_fixnum().unwrap_or(0);
                    result.push(cp as u8 as char);
                    lst = self.heap.cdr(lst);
                }
                self.make_string(&result)
            }

            // Vector conversions
            79 => { // vector->list
                let mut elems = self.heap.rib_car(a1);
                let mut result = Vec::new();
                while self.heap.is_pair(elems) {
                    result.push(self.heap.car(elems));
                    elems = self.heap.cdr(elems);
                }
                self.heap.list(&result)
            }
            80 => { // list->vector
                let len = self.heap.length(a1) as i64;
                let mut elems = Val::NIL;
                let mut items = Vec::new();
                let mut lst = a1;
                while self.heap.is_pair(lst) {
                    items.push(self.heap.car(lst));
                    lst = self.heap.cdr(lst);
                }
                for &v in items.iter().rev() {
                    elems = self.heap.cons(v, elems);
                }
                self.heap.vector(elems, Val::fixnum(len))
            }

            // Char comparisons
            81 => { // char=?
                let ca = self.heap.rib_car(a1).as_fixnum();
                let cb = self.heap.rib_car(a2).as_fixnum();
                self.scheme_bool(ca == cb)
            }
            82 => { // char<?
                let ca = self.heap.rib_car(a1).as_fixnum().unwrap_or(0);
                let cb = self.heap.rib_car(a2).as_fixnum().unwrap_or(0);
                self.scheme_bool(ca < cb)
            }
            83 => { // char-alphabetic?
                let cp = self.heap.rib_car(a1).as_fixnum().unwrap_or(0) as u8;
                self.scheme_bool(cp.is_ascii_alphabetic())
            }
            84 => { // char-numeric?
                let cp = self.heap.rib_car(a1).as_fixnum().unwrap_or(0) as u8;
                self.scheme_bool(cp.is_ascii_digit())
            }
            85 => { // char-whitespace?
                let cp = self.heap.rib_car(a1).as_fixnum().unwrap_or(0) as u8;
                self.scheme_bool(cp.is_ascii_whitespace())
            }
            86 => { // char-upper-case?
                let cp = self.heap.rib_car(a1).as_fixnum().unwrap_or(0) as u8;
                self.scheme_bool(cp.is_ascii_uppercase())
            }
            87 => { // char-lower-case?
                let cp = self.heap.rib_car(a1).as_fixnum().unwrap_or(0) as u8;
                self.scheme_bool(cp.is_ascii_lowercase())
            }
            88 => { // char-upcase
                let cp = self.heap.rib_car(a1).as_fixnum().unwrap_or(0) as u8;
                self.heap.character(cp.to_ascii_uppercase() as i64)
            }
            89 => { // char-downcase
                let cp = self.heap.rib_car(a1).as_fixnum().unwrap_or(0) as u8;
                self.heap.character(cp.to_ascii_lowercase() as i64)
            }

            // string-set!
            90 => {
                let idx = a2.as_fixnum().unwrap_or(0);
                let a3 = self.heap.car(self.heap.cdr(self.heap.cdr(args)));
                let cp = self.heap.rib_car(a3).as_fixnum().unwrap_or(0);
                let mut chars = self.heap.rib_car(a1);
                for _ in 0..idx { chars = self.heap.cdr(chars); }
                self.heap.set_car(chars, Val::fixnum(cp));
                self.void_val
            }

            // Number type predicates
            91 => self.scheme_bool(a1.is_fixnum()),           // integer?
            92 => self.scheme_bool(a1.is_fixnum()),           // exact?
            93 => self.scheme_bool(false),                     // inexact? (no inexact numbers)

            // expt
            94 => {
                let base = a1.as_fixnum().unwrap_or(0);
                let exp = a2.as_fixnum().unwrap_or(0);
                let mut result = 1i64;
                for _ in 0..exp { result *= base; }
                Val::fixnum(result)
            }

            // More string comparisons
            95 => { // string>?
                let sa = self.extract_string(a1).unwrap_or_default();
                let sb = self.extract_string(a2).unwrap_or_default();
                self.scheme_bool(sa > sb)
            }
            96 => { // string<=?
                let sa = self.extract_string(a1).unwrap_or_default();
                let sb = self.extract_string(a2).unwrap_or_default();
                self.scheme_bool(sa <= sb)
            }
            97 => { // string>=?
                let sa = self.extract_string(a1).unwrap_or_default();
                let sb = self.extract_string(a2).unwrap_or_default();
                self.scheme_bool(sa >= sb)
            }

            // More char comparisons
            98 => { // char>?
                let ca = self.heap.rib_car(a1).as_fixnum().unwrap_or(0);
                let cb = self.heap.rib_car(a2).as_fixnum().unwrap_or(0);
                self.scheme_bool(ca > cb)
            }
            99 => { // char<=?
                let ca = self.heap.rib_car(a1).as_fixnum().unwrap_or(0);
                let cb = self.heap.rib_car(a2).as_fixnum().unwrap_or(0);
                self.scheme_bool(ca <= cb)
            }
            100 => { // char>=?
                let ca = self.heap.rib_car(a1).as_fixnum().unwrap_or(0);
                let cb = self.heap.rib_car(a2).as_fixnum().unwrap_or(0);
                self.scheme_bool(ca >= cb)
            }

            // eof-object?
            101 => self.scheme_bool(self.heap.tag(a1) == table::EOF),

            // write-char
            102 => {
                let cp = self.heap.rib_car(a1).as_fixnum().unwrap_or(0);
                print!("{}", cp as u8 as char);
                self.void_val
            }

            // error
            103 => {
                eprint!("Error");
                if self.heap.is_string(a1) {
                    if let Some(s) = self.extract_string(a1) {
                        eprint!(": {s}");
                    }
                }
                eprintln!();
                Val::NIL
            }

            // ── Algebra extension ─────────────────────────────
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

            _ => Val::NIL,
        }
    }

    // ── Helpers ──────────────────────────────────────────────────

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
        } else {
            false
        }
    }

    fn append(&mut self, a: Val, b: Val) -> Val {
        if !self.heap.is_pair(a) { return b; }
        let car = self.heap.car(a);
        let rest = self.append(self.heap.cdr(a), b);
        self.heap.cons(car, rest)
    }

    fn builtin_map(&mut self, proc: Val, lst: Val) -> Val {
        if !self.heap.is_pair(lst) { return Val::NIL; }
        let arg = self.heap.car(lst);
        let arg_list = self.heap.cons(arg, Val::NIL);
        let val = self.apply(proc, arg_list);
        let rest = self.builtin_map(proc, self.heap.cdr(lst));
        self.heap.cons(val, rest)
    }

    fn builtin_for_each(&mut self, proc: Val, mut lst: Val) {
        while self.heap.is_pair(lst) {
            let arg = self.heap.car(lst);
            let arg_list = self.heap.cons(arg, Val::NIL);
            self.apply(proc, arg_list);
            lst = self.heap.cdr(lst);
        }
    }

    // ── Display / Write ──────────────────────────────────────────

    pub fn display(&self, v: Val) {
        if v == Val::NIL {
            print!("()");
        } else if v.is_fixnum() {
            print!("{}", v.as_fixnum().unwrap());
        } else if v == self.true_val {
            print!("#t");
        } else if v == self.false_val {
            print!("#f");
        } else {
            let tag = self.heap.tag(v);
            match tag {
                t if t == table::T_PAIR => {
                    print!("(");
                    self.display(self.heap.car(v));
                    let mut rest = self.heap.cdr(v);
                    while self.heap.is_pair(rest) {
                        print!(" ");
                        self.display(self.heap.car(rest));
                        rest = self.heap.cdr(rest);
                    }
                    if rest != Val::NIL {
                        print!(" . ");
                        self.display(rest);
                    }
                    print!(")");
                }
                t if t == table::T_SYM => {
                    if let Some(name) = self.syms.symbol_name(v) {
                        print!("{name}");
                    } else {
                        print!("<sym>");
                    }
                }
                t if t == table::T_STR => {
                    if let Some(s) = self.extract_string(v) {
                        print!("{s}");
                    }
                }
                t if t == table::T_CHAR => {
                    let cp = self.heap.rib_car(v).as_fixnum().unwrap_or(0);
                    print!("{}", cp as u8 as char);
                }
                t if t == table::T_CLS => print!("<procedure>"),
                t if t == table::T_VEC => {
                    print!("#(");
                    let mut elems = self.heap.rib_car(v);
                    let mut first = true;
                    while self.heap.is_pair(elems) {
                        if !first { print!(" "); }
                        self.display(self.heap.car(elems));
                        elems = self.heap.cdr(elems);
                        first = false;
                    }
                    print!(")");
                }
                t if t == table::VOID => print!("<void>"),
                t if t == table::EOF => print!("<eof>"),
                _ => print!("<unknown:{tag}>"),
            }
        }
    }

    pub fn write(&self, v: Val) {
        // Write is like display but strings get quotes
        if self.heap.is_string(v) {
            print!("\"");
            if let Some(s) = self.extract_string(v) {
                for c in s.chars() {
                    match c {
                        '"' => print!("\\\""),
                        '\\' => print!("\\\\"),
                        '\n' => print!("\\n"),
                        _ => print!("{c}"),
                    }
                }
            }
            print!("\"");
        } else if self.heap.tag(v) == table::T_CHAR {
            let cp = self.heap.rib_car(v).as_fixnum().unwrap_or(0);
            match cp as u8 {
                b' ' => print!("#\\space"),
                b'\n' => print!("#\\newline"),
                c => print!("#\\{}", c as char),
            }
        } else {
            self.display(v);
        }
    }

    // ── Top-level interface ──────────────────────────────────────

    /// Evaluate a string of Scheme source code.
    /// Returns the value of the last expression.
    pub fn eval_str(&mut self, src: &str) -> Val {
        let exprs = crate::reader::read_all(src, &mut self.heap, &mut self.syms)
            .unwrap_or_default();
        let mut result = self.void_val;
        let env = Val::NIL;
        for expr in exprs {
            result = self.eval(expr, env);
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn eval_fixnum() {
        let mut ev = Eval::new();
        assert_eq!(ev.eval_str("42"), Val::fixnum(42));
    }

    #[test]
    fn eval_arithmetic() {
        let mut ev = Eval::new();
        assert_eq!(ev.eval_str("(+ 3 4)"), Val::fixnum(7));
        assert_eq!(ev.eval_str("(- 10 3)"), Val::fixnum(7));
        assert_eq!(ev.eval_str("(* 6 7)"), Val::fixnum(42));
        assert_eq!(ev.eval_str("(quotient 10 3)"), Val::fixnum(3));
        assert_eq!(ev.eval_str("(remainder 10 3)"), Val::fixnum(1));
    }

    #[test]
    fn eval_nested() {
        let mut ev = Eval::new();
        assert_eq!(ev.eval_str("(+ (* 3 4) (* 5 6))"), Val::fixnum(42));
    }

    #[test]
    fn eval_if() {
        let mut ev = Eval::new();
        assert_eq!(ev.eval_str("(if #t 1 2)"), Val::fixnum(1));
        assert_eq!(ev.eval_str("(if #f 1 2)"), Val::fixnum(2));
    }

    #[test]
    fn eval_define_and_ref() {
        let mut ev = Eval::new();
        ev.eval_str("(define x 42)");
        assert_eq!(ev.eval_str("x"), Val::fixnum(42));
    }

    #[test]
    fn eval_lambda() {
        let mut ev = Eval::new();
        assert_eq!(ev.eval_str("((lambda (x) (+ x 1)) 41)"), Val::fixnum(42));
    }

    #[test]
    fn eval_define_function() {
        let mut ev = Eval::new();
        ev.eval_str("(define (add a b) (+ a b))");
        assert_eq!(ev.eval_str("(add 3 4)"), Val::fixnum(7));
    }

    #[test]
    fn eval_recursion() {
        let mut ev = Eval::new();
        ev.eval_str("(define (fact n) (if (= n 0) 1 (* n (fact (- n 1)))))");
        assert_eq!(ev.eval_str("(fact 10)"), Val::fixnum(3628800));
    }

    #[test]
    fn eval_fib() {
        let mut ev = Eval::new();
        ev.eval_str("(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))");
        assert_eq!(ev.eval_str("(fib 10)"), Val::fixnum(55));
    }

    #[test]
    fn eval_list_ops() {
        let mut ev = Eval::new();
        assert_eq!(ev.eval_str("(car (cons 1 2))"), Val::fixnum(1));
        assert_eq!(ev.eval_str("(cdr (cons 1 2))"), Val::fixnum(2));
        assert_eq!(ev.eval_str("(length (list 1 2 3))"), Val::fixnum(3));
    }

    #[test]
    fn eval_let() {
        let mut ev = Eval::new();
        assert_eq!(ev.eval_str("(let ((x 10) (y 20)) (+ x y))"), Val::fixnum(30));
    }

    #[test]
    fn eval_cond() {
        let mut ev = Eval::new();
        assert_eq!(ev.eval_str("(cond (#f 1) (#t 2) (else 3))"), Val::fixnum(2));
    }

    #[test]
    fn eval_and_or() {
        let mut ev = Eval::new();
        assert_eq!(ev.eval_str("(and 1 2 3)"), Val::fixnum(3));
        assert_eq!(ev.eval_str("(or #f #f 42)"), Val::fixnum(42));
    }

    #[test]
    fn eval_tail_recursion() {
        let mut ev = Eval::new();
        ev.eval_str("(define (loop n) (if (= n 0) 0 (loop (- n 1))))");
        // This would stack overflow without tail call optimization
        assert_eq!(ev.eval_str("(loop 100000)"), Val::fixnum(0));
    }

    #[test]
    fn eval_closures() {
        let mut ev = Eval::new();
        ev.eval_str("(define (make-adder n) (lambda (x) (+ x n)))");
        ev.eval_str("(define add10 (make-adder 10))");
        assert_eq!(ev.eval_str("(add10 32)"), Val::fixnum(42));
    }

    #[test]
    fn eval_map() {
        let mut ev = Eval::new();
        ev.eval_str("(define (double x) (* x 2))");
        let result = ev.eval_str("(map double (list 1 2 3))");
        let mut ev2 = ev;
        assert_eq!(ev2.heap.car(result), Val::fixnum(2));
        assert_eq!(ev2.heap.car(ev2.heap.cdr(result)), Val::fixnum(4));
        assert_eq!(ev2.heap.car(ev2.heap.cdr(ev2.heap.cdr(result))), Val::fixnum(6));
    }

    #[test]
    fn eval_nqueens() {
        let mut ev = Eval::new();
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

    #[test]
    fn eval_let_star() {
        let mut ev = Eval::new();
        assert_eq!(ev.eval_str("(let* ((x 1) (y (+ x 1))) y)"), Val::fixnum(2));
    }

    #[test]
    fn eval_named_let() {
        let mut ev = Eval::new();
        assert_eq!(
            ev.eval_str("(let loop ((n 10) (acc 0)) (if (= n 0) acc (loop (- n 1) (+ acc n))))"),
            Val::fixnum(55)
        );
    }

    #[test]
    fn eval_case() {
        let mut ev = Eval::new();
        assert_eq!(ev.eval_str("(case 2 ((1) 10) ((2) 20) ((3) 30))"), Val::fixnum(20));
        assert_eq!(ev.eval_str("(case 9 ((1) 10) (else 99))"), Val::fixnum(99));
    }

    #[test]
    fn eval_do() {
        let mut ev = Eval::new();
        // Sum 1 to 10 using do
        assert_eq!(
            ev.eval_str("(do ((i 1 (+ i 1)) (sum 0 (+ sum i))) ((> i 10) sum))"),
            Val::fixnum(55)
        );
    }

    #[test]
    fn eval_multi_body_lambda() {
        let mut ev = Eval::new();
        ev.eval_str("(define x 0)");
        ev.eval_str("(define (f) (set! x 1) (set! x (+ x 1)) x)");
        assert_eq!(ev.eval_str("(f)"), Val::fixnum(2));
    }

    #[test]
    fn eval_multi_body_define() {
        let mut ev = Eval::new();
        ev.eval_str("(define (g n) (define m (* n 2)) (+ m 1))");
        assert_eq!(ev.eval_str("(g 5)"), Val::fixnum(11));
    }

    #[test]
    fn eval_list_ref() {
        let mut ev = Eval::new();
        assert_eq!(ev.eval_str("(list-ref (list 10 20 30) 1)"), Val::fixnum(20));
    }

    #[test]
    fn eval_assoc() {
        let mut ev = Eval::new();
        let result = ev.eval_str("(cdr (assv 2 (list (cons 1 10) (cons 2 20) (cons 3 30))))");
        assert_eq!(result, Val::fixnum(20));
    }

    #[test]
    fn eval_string_ops() {
        let mut ev = Eval::new();
        assert_eq!(ev.eval_str("(string-length \"hello\")"), Val::fixnum(5));
        let r1 = ev.eval_str("(string=? \"abc\" \"abc\")");
        assert!(ev.is_true(r1));
        let r2 = ev.eval_str("(string=? \"abc\" \"def\")");
        assert!(!ev.is_true(r2));
    }

    #[test]
    fn eval_char_ops() {
        let mut ev = Eval::new();
        assert_eq!(ev.eval_str("(char->integer #\\A)"), Val::fixnum(65));
        let r1 = ev.eval_str("(char-alphabetic? #\\a)");
        assert!(ev.is_true(r1));
        let r2 = ev.eval_str("(char-alphabetic? #\\1)");
        assert!(!ev.is_true(r2));
    }

    #[test]
    fn eval_division() {
        let mut ev = Eval::new();
        assert_eq!(ev.eval_str("(/ 10 3)"), Val::fixnum(3));
        assert_eq!(ev.eval_str("(expt 2 10)"), Val::fixnum(1024));
    }

    #[test]
    fn eval_call_cc_escape() {
        let mut ev = Eval::new();
        assert_eq!(
            ev.eval_str("(call-with-current-continuation (lambda (k) (+ 1 (k 42))))"),
            Val::fixnum(42)
        );
    }

    #[test]
    fn eval_call_cc_no_escape() {
        let mut ev = Eval::new();
        assert_eq!(
            ev.eval_str("(call-with-current-continuation (lambda (k) 99))"),
            Val::fixnum(99)
        );
    }

    #[test]
    fn eval_quasiquote() {
        let mut ev = Eval::new();
        ev.eval_str("(define x 42)");
        let result = ev.eval_str("`(1 ,x 3)");
        assert_eq!(ev.heap.car(result), Val::fixnum(1));
        assert_eq!(ev.heap.car(ev.heap.cdr(result)), Val::fixnum(42));
        assert_eq!(ev.heap.car(ev.heap.cdr(ev.heap.cdr(result))), Val::fixnum(3));
    }

    #[test]
    fn eval_rest_params() {
        let mut ev = Eval::new();
        ev.eval_str("(define (f x . rest) rest)");
        let result = ev.eval_str("(f 1 2 3)");
        assert_eq!(ev.heap.car(result), Val::fixnum(2));
        assert_eq!(ev.heap.car(ev.heap.cdr(result)), Val::fixnum(3));
    }

    #[test]
    fn eval_fib_iterative_named_let() {
        let mut ev = Eval::new();
        ev.eval_str("
            (define (fib-iter n)
              (let loop ((i n) (a 0) (b 1))
                (if (= i 0) a
                    (loop (- i 1) b (+ a b)))))
        ");
        assert_eq!(ev.eval_str("(fib-iter 30)"), Val::fixnum(832040));
    }

    #[test]
    fn eval_reverse() {
        let mut ev = Eval::new();
        let result = ev.eval_str("(reverse (list 1 2 3))");
        assert_eq!(ev.heap.car(result), Val::fixnum(3));
        assert_eq!(ev.heap.car(ev.heap.cdr(result)), Val::fixnum(2));
        assert_eq!(ev.heap.car(ev.heap.cdr(ev.heap.cdr(result))), Val::fixnum(1));
    }

    // ── Algebra extension tests ──────────────────────────────

    #[test]
    fn algebra_dot() {
        let mut ev = Eval::new();
        // CAR applied to T_PAIR type tag → T_PAIR (valid)
        assert_eq!(ev.eval_str("(dot CAR T_PAIR)"), Val::fixnum(table::T_PAIR as i64));
        // CAR applied to T_STR type tag → BOT (error)
        assert_eq!(ev.eval_str("(dot CAR T_STR)"), Val::fixnum(table::BOT as i64));
    }

    #[test]
    fn algebra_tau() {
        let mut ev = Eval::new();
        // tau of a pair → T_PAIR
        assert_eq!(ev.eval_str("(tau (cons 1 2))"), Val::fixnum(table::T_PAIR as i64));
        // tau of nil → TOP
        assert_eq!(ev.eval_str("(tau '())"), Val::fixnum(table::TOP as i64));
        // tau of a string → T_STR
        assert_eq!(ev.eval_str("(tau \"hello\")"), Val::fixnum(table::T_STR as i64));
    }

    #[test]
    fn algebra_type_valid() {
        let mut ev = Eval::new();
        let r1 = ev.eval_str("(type-valid? CAR T_PAIR)");
        assert!(ev.is_true(r1));
        let r2 = ev.eval_str("(type-valid? CAR T_STR)");
        assert!(!ev.is_true(r2));
        let r3 = ev.eval_str("(type-valid? CAR T_SYM)");
        assert!(!ev.is_true(r3));
    }

    #[test]
    fn algebra_elements_bound() {
        let mut ev = Eval::new();
        assert_eq!(ev.eval_str("TOP"), Val::fixnum(0));
        assert_eq!(ev.eval_str("BOT"), Val::fixnum(1));
        assert_eq!(ev.eval_str("T_PAIR"), Val::fixnum(table::T_PAIR as i64));
        assert_eq!(ev.eval_str("Y"), Val::fixnum(table::Y as i64));
    }

    #[test]
    fn algebra_user_dispatcher() {
        let mut ev = Eval::new();
        // Build a user-space type dispatcher from tau and dot
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
    fn algebra_retraction() {
        let mut ev = Eval::new();
        // The Q/E retraction: dot(E, dot(Q, x)) = x for core elements
        // We can verify this from Scheme
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
    fn algebra_y_fixed_point() {
        let mut ev = Eval::new();
        // Y(RHO) is a fixed point of RHO: dot(RHO, dot(Y, RHO)) = dot(Y, RHO)
        let yp = ev.eval_str("(dot Y RHO)");
        let ryp = ev.eval_str("(dot RHO (dot Y RHO))");
        assert_eq!(yp, ryp);
        // And it's not an absorber
        let r = ev.eval_str("(> (dot Y RHO) 1)");
        assert!(ev.is_true(r));
    }

    #[test]
    fn algebra_enumerate_valid_ops() {
        let mut ev = Eval::new();
        // The programmer can ask: which operations are valid on pairs?
        // This is the "introspect the capability matrix" use case
        ev.eval_str("
            (define (count-valid-ops type-tag)
              (let loop ((op 0) (count 0))
                (if (= op 12)
                    count
                    (loop (+ op 1)
                          (+ count (if (type-valid? op type-tag) 1 0))))))
        ");
        // Pairs should have more valid operations than strings
        let pair_ops = ev.eval_str("(count-valid-ops T_PAIR)");
        let str_ops = ev.eval_str("(count-valid-ops T_STR)");
        // At minimum, CAR and CDR are valid on pairs
        assert!(pair_ops.as_fixnum().unwrap() >= 2);
        // CAR and CDR are NOT valid on strings
        assert!(str_ops.as_fixnum().unwrap() < pair_ops.as_fixnum().unwrap());
    }
}
