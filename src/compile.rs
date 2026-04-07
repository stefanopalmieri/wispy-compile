//! Scheme → Rust compiler.
//!
//! Compiles Scheme source into a standalone Rust program with inline
//! table + heap, no external dependencies.
//!
//! Handles: R4RS core (define, lambda, if, cond, let/let*/letrec,
//! begin, and/or, quote, set!, do, case), closures, TCO,
//! define-syntax/syntax-rules, strings, chars, vectors.
//!
//! R7RS: case-lambda, define-record-type, values/call-with-values,
//! guard/raise/error, with-exception-handler, define-library/import.

use crate::heap::Heap;
use crate::symbol::SymbolTable;
use crate::val::Val;
use crate::table;

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};

/// A clause for case-lambda: (params, body_list).
#[derive(Clone)]
struct CaseClause {
    params: Vec<String>,
    rest_param: Option<String>,
    body_list: Val,
}

/// A lambda that has been lifted to a top-level function.
#[derive(Clone)]
struct LiftedLambda {
    id: usize,
    params: Vec<String>,
    rest_param: Option<String>,
    free_vars: Vec<String>,
    body_list: Val, // list of body expressions (use emit_begin)
    /// If Some, this is a case-lambda with multiple dispatch clauses.
    case_clauses: Option<Vec<CaseClause>>,
}

/// TCO context for the function currently being compiled.
#[derive(Clone)]
struct TcoContext {
    fn_name: String,
    params: Vec<String>,
}

/// A user-defined library (compile-time resolution).
struct Library {
    /// Library name parts, e.g. ["mylib"] or ["my", "lib"]
    name: Vec<String>,
    /// Exported symbol names
    exports: Vec<String>,
}

/// A record type defined via define-record-type.
struct RecordType {
    type_id: usize,
    constructor_name: String,
    constructor_fields: Vec<String>, // field names in constructor order
    predicate_name: String,
    accessors: Vec<(usize, String)>, // (field_index, accessor_name)
    mutators: Vec<(usize, String)>,  // (field_index, mutator_name)
}

/// A top-level function definition.
struct Function {
    name: String,
    params: Vec<String>,
    rest_param: Option<String>,
    body: Val,
}

/// Compiler state.
pub struct Compiler {
    /// Collected top-level function definitions
    functions: Vec<Function>,
    /// Top-level expressions to run in main
    main_exprs: Vec<Val>,
    /// Global variable definitions: (name, init_expr)
    globals: Vec<(String, Val)>,
    /// Lifted lambda functions (populated during code generation)
    lifted: RefCell<Vec<LiftedLambda>>,
    /// Next lambda ID to assign (starts at functions.len())
    next_lambda_id: Cell<usize>,
    /// Current function's TCO context (set during function body emission)
    tco: RefCell<Option<TcoContext>>,
    /// Variables that are targets of set! (need let mut)
    set_targets: RefCell<HashSet<String>>,
    /// Record types defined via define-record-type
    record_types: Vec<RecordType>,
    /// User-defined libraries
    libraries: Vec<Library>,
    /// Builtin closures: maps builtin name to its lambda ID
    builtin_closures: RefCell<HashMap<String, usize>>,
    /// Parameters of the currently-emitting function (to avoid direct-call for shadowed names)
    current_params: RefCell<HashSet<String>>,
}

impl Compiler {
    pub fn new() -> Self {
        Compiler {
            functions: Vec::new(),
            main_exprs: Vec::new(),
            globals: Vec::new(),
            lifted: RefCell::new(Vec::new()),
            next_lambda_id: Cell::new(0),
            tco: RefCell::new(None),
            set_targets: RefCell::new(HashSet::new()),
            record_types: Vec::new(),
            libraries: Vec::new(),
            builtin_closures: RefCell::new(HashMap::new()),
            current_params: RefCell::new(HashSet::new()),
        }
    }

    /// Scan an expression tree and collect all variables that are targets of set!.
    fn collect_set_targets(&self, expr: Val, heap: &Heap, syms: &SymbolTable) {
        if !heap.is_pair(expr) || heap.tag(expr) != table::T_PAIR {
            return;
        }
        let head = heap.car(expr);
        let rest = heap.cdr(expr);
        if heap.is_symbol(head) {
            let name = syms.symbol_name(head).unwrap_or("");
            if name == "set!" {
                let var = heap.car(rest);
                if heap.is_symbol(var) {
                    if let Some(vname) = syms.symbol_name(var) {
                        self.set_targets.borrow_mut().insert(vname.to_string());
                    }
                }
                self.collect_set_targets(heap.car(heap.cdr(rest)), heap, syms);
                return;
            }
        }
        // Recurse into all sub-expressions
        let mut r = expr;
        while heap.is_pair(r) {
            self.collect_set_targets(heap.car(r), heap, syms);
            r = heap.cdr(r);
        }
    }

    /// Check if a variable is a set! target (needs let mut).
    fn is_set_target(&self, name: &str) -> bool {
        self.set_targets.borrow().contains(name)
    }

    /// Parse and collect top-level forms, expanding macros.
    pub fn process(&mut self, exprs: &[Val], heap: &mut Heap, syms: &mut SymbolTable) {
        let mut macros: Vec<(Val, crate::macros::Macro)> = Vec::new();
        for &expr in exprs {
            if heap.is_pair(expr) {
                let head = heap.car(expr);
                if heap.is_symbol(head) {
                    if let Some(name) = syms.symbol_name(head) {
                        if name == "define-syntax" {
                            let rest = heap.cdr(expr);
                            let name_sym = heap.car(rest);
                            let transformer = heap.car(heap.cdr(rest));
                            if let Some(mac) = crate::macros::parse_syntax_rules(
                                transformer, heap, syms
                            ) {
                                macros.push((name_sym, mac));
                            }
                            continue;
                        }
                        if name == "define" {
                            let expanded = self.expand_all(expr, &macros, heap, syms);
                            self.process_define(expanded, heap, syms);
                            continue;
                        }
                        if name == "define-record-type" {
                            self.process_record_type(expr, heap, syms);
                            continue;
                        }
                        if name == "define-library" {
                            self.process_library(expr, heap, syms, &macros);
                            continue;
                        }
                        if name == "import" {
                            // (import (lib-name ...)) — built-in libs are no-ops,
                            // user libs already processed in define-library
                            continue;
                        }
                    }
                }
            }
            let expanded = self.expand_all(expr, &macros, heap, syms);
            self.main_exprs.push(expanded);
        }
        // Pre-scan for set! targets so we can emit let mut where needed
        for &expr in &self.main_exprs {
            self.collect_set_targets(expr, heap, syms);
        }
        for func in &self.functions {
            self.collect_set_targets(func.body, heap, syms);
        }
    }

    /// Recursively expand all macros in an expression.
    fn expand_all(&self, expr: Val, macros: &[(Val, crate::macros::Macro)],
                  heap: &mut Heap, syms: &SymbolTable) -> Val {
        if !heap.is_pair(expr) { return expr; }
        let head = heap.car(expr);
        // Check if head is a macro name
        if heap.is_symbol(head) {
            let mac = macros.iter().find(|(n, _)| *n == head).map(|(_, m)| m);
            if let Some(mac) = mac {
                if let Some(expanded) = crate::macros::expand_macro(mac, expr, heap, syms) {
                    return self.expand_all(expanded, macros, heap, syms);
                }
            }
        }
        // Recursively expand in sub-expressions
        let car = heap.car(expr);
        let cdr = heap.cdr(expr);
        let new_car = self.expand_all(car, macros, heap, syms);
        let new_cdr = self.expand_all_list(cdr, macros, heap, syms);
        heap.cons(new_car, new_cdr)
    }

    fn expand_all_list(&self, mut list: Val, macros: &[(Val, crate::macros::Macro)],
                       heap: &mut Heap, syms: &SymbolTable) -> Val {
        if !heap.is_pair(list) { return list; }
        let mut items = Vec::new();
        while heap.is_pair(list) {
            items.push(self.expand_all(heap.car(list), macros, heap, syms));
            list = heap.cdr(list);
        }
        let mut result = list; // preserve tail (NIL or dotted)
        for v in items.iter().rev() {
            result = heap.cons(*v, result);
        }
        result
    }

    fn process_define(&mut self, expr: Val, heap: &mut Heap, syms: &mut SymbolTable) {
        let rest = heap.cdr(expr);
        let target = heap.car(rest);

        if heap.is_symbol(target) {
            // (define x expr)
            let name = syms.symbol_name(target).unwrap_or("_").to_string();
            let init = heap.car(heap.cdr(rest));
            self.globals.push((name, init));
        } else if heap.is_pair(target) {
            // (define (f args...) body...)
            let name_sym = heap.car(target);
            let name = syms.symbol_name(name_sym).unwrap_or("_").to_string();
            let mut params = Vec::new();
            let mut p = heap.cdr(target);
            while heap.is_pair(p) {
                let param = heap.car(p);
                if let Some(pname) = syms.symbol_name(param) {
                    params.push(pname.to_string());
                }
                p = heap.cdr(p);
            }
            // Check for rest param (dotted tail)
            let rest_param = if heap.is_symbol(p) {
                syms.symbol_name(p).map(|s| s.to_string())
            } else { None };
            // Collect body (may be multiple expressions), hoisting internal defines
            let mut body_list = heap.cdr(rest);
            body_list = self.hoist_internal_defines(body_list, heap, syms);
            let body = if heap.cdr(body_list) == Val::NIL {
                heap.car(body_list)
            } else {
                // Wrap in (begin body1 body2 ...)
                let begin_sym = syms.intern("begin", heap);
                heap.cons(begin_sym, body_list)
            };
            self.functions.push(Function { name, params, rest_param, body });
        }
    }

    /// Convert leading internal `define` forms into a `letrec` wrapping the remaining body.
    /// (define (f x) (define (g y) ...) (define h 1) body...)
    /// → (define (f x) (letrec ((g (lambda (y) ...)) (h 1)) body...))
    fn hoist_internal_defines(&mut self, mut body_list: Val, heap: &mut Heap, syms: &mut SymbolTable) -> Val {
        // Pre-intern symbols we'll need
        let lambda_sym = syms.intern("lambda", heap);
        let letrec_sym = syms.intern("letrec", heap);

        let mut bindings = Vec::new();
        loop {
            if !heap.is_pair(body_list) { break; }
            let expr = heap.car(body_list);
            if !heap.is_pair(expr) { break; }
            let head = heap.car(expr);
            if !heap.is_symbol(head) { break; }
            if syms.symbol_name(head) != Some("define") { break; }

            let rest = heap.cdr(expr);
            let target = heap.car(rest);
            if heap.is_symbol(target) {
                // (define x expr) → binding (x expr)
                let init = heap.car(heap.cdr(rest));
                let init_list = heap.cons(init, Val::NIL);
                let binding = heap.cons(target, init_list);
                bindings.push(binding);
            } else if heap.is_pair(target) {
                // (define (f args...) body...) → binding (f (lambda (args...) body...))
                let name_sym = heap.car(target);
                let params = heap.cdr(target);
                let fn_body = heap.cdr(rest);
                let params_body = heap.cons(params, fn_body);
                let lambda_expr = heap.cons(lambda_sym, params_body);
                let lambda_list = heap.cons(lambda_expr, Val::NIL);
                let binding = heap.cons(name_sym, lambda_list);
                bindings.push(binding);
            }
            body_list = heap.cdr(body_list);
        }
        if bindings.is_empty() {
            return body_list;
        }
        // Build (letrec ((name init) ...) body...)
        let mut bindings_list = Val::NIL;
        for b in bindings.iter().rev() {
            bindings_list = heap.cons(*b, bindings_list);
        }
        let bindings_body = heap.cons(bindings_list, body_list);
        let letrec_expr = heap.cons(letrec_sym, bindings_body);
        heap.cons(letrec_expr, Val::NIL)
    }

    /// Parse a define-record-type form and register the record type.
    fn process_record_type(&mut self, expr: Val, heap: &Heap, syms: &SymbolTable) {
        let rest = heap.cdr(expr);
        // (define-record-type <name> (constructor field...) predicate (field accessor [mutator])...)
        let _type_name = heap.car(rest); // <name> — not used at runtime
        let rest2 = heap.cdr(rest);
        let constructor = heap.car(rest2);
        let rest3 = heap.cdr(rest2);
        let predicate_sym = heap.car(rest3);
        let field_specs = heap.cdr(rest3);

        let type_id = self.record_types.len();
        let constructor_name = syms.symbol_name(heap.car(constructor)).unwrap_or("_").to_string();
        let predicate_name = syms.symbol_name(predicate_sym).unwrap_or("_").to_string();

        // Constructor field names (in order)
        let mut constructor_fields = Vec::new();
        let mut p = heap.cdr(constructor);
        while heap.is_pair(p) {
            if let Some(fname) = syms.symbol_name(heap.car(p)) {
                constructor_fields.push(fname.to_string());
            }
            p = heap.cdr(p);
        }

        // Field specs: (field accessor [mutator])
        let mut accessors = Vec::new();
        let mut mutators = Vec::new();
        let mut fs = field_specs;
        while heap.is_pair(fs) {
            let spec = heap.car(fs);
            let field_name = syms.symbol_name(heap.car(spec)).unwrap_or("_").to_string();
            let accessor_name = syms.symbol_name(heap.car(heap.cdr(spec))).unwrap_or("_").to_string();
            // Find field index in constructor order
            let idx = constructor_fields.iter().position(|f| f == &field_name).unwrap_or(0);
            accessors.push((idx, accessor_name));
            // Check for mutator
            let mutator_rest = heap.cdr(heap.cdr(spec));
            if heap.is_pair(mutator_rest) {
                let mutator_name = syms.symbol_name(heap.car(mutator_rest)).unwrap_or("_").to_string();
                mutators.push((idx, mutator_name));
            }
            fs = heap.cdr(fs);
        }

        self.record_types.push(RecordType {
            type_id,
            constructor_name,
            constructor_fields,
            predicate_name,
            accessors,
            mutators,
        });
    }

    /// Parse a define-library form and process its body.
    fn process_library(&mut self, expr: Val, heap: &mut Heap, syms: &mut SymbolTable,
                       macros: &[(Val, crate::macros::Macro)]) {
        let rest = heap.cdr(expr);
        let name_list = heap.car(rest);
        let decls = heap.cdr(rest);

        // Extract library name: (name part1 part2 ...)
        let mut lib_name = Vec::new();
        let mut n = name_list;
        while heap.is_pair(n) {
            if let Some(s) = syms.symbol_name(heap.car(n)) {
                lib_name.push(s.to_string());
            }
            n = heap.cdr(n);
        }

        // Process declarations: export, import (ignored), begin
        let mut exports = Vec::new();
        let mut d = decls;
        while heap.is_pair(d) {
            let decl = heap.car(d);
            if heap.is_pair(decl) {
                let dhead = heap.car(decl);
                if let Some(dname) = syms.symbol_name(dhead) {
                    match dname {
                        "export" => {
                            let mut e = heap.cdr(decl);
                            while heap.is_pair(e) {
                                if let Some(ename) = syms.symbol_name(heap.car(e)) {
                                    exports.push(ename.to_string());
                                }
                                e = heap.cdr(e);
                            }
                        }
                        "begin" => {
                            // Process body definitions as top-level
                            let mut body = heap.cdr(decl);
                            while heap.is_pair(body) {
                                let form = heap.car(body);
                                let expanded = self.expand_all(form, macros, heap, syms);
                                if heap.is_pair(expanded) {
                                    let fhead = heap.car(expanded);
                                    if heap.is_symbol(fhead) {
                                        if let Some(fname) = syms.symbol_name(fhead) {
                                            if fname == "define" {
                                                self.process_define(expanded, heap, syms);
                                                body = heap.cdr(body);
                                                continue;
                                            }
                                            if fname == "define-record-type" {
                                                self.process_record_type(expanded, heap, syms);
                                                body = heap.cdr(body);
                                                continue;
                                            }
                                        }
                                    }
                                }
                                // Non-define forms in library body (unusual but legal)
                                self.main_exprs.push(expanded);
                                body = heap.cdr(body);
                            }
                        }
                        _ => {} // import, cond-expand, etc. — ignored
                    }
                }
            }
            d = heap.cdr(d);
        }

        self.libraries.push(Library { name: lib_name, exports });
    }

    // ── TCO helpers ────────────────────────────────────────────────

    /// Check if an expression contains a self-tail-call to `fn_name`.
    /// Walks into tail positions only: if branches, begin last, let/let*/letrec body.
    fn has_self_tail_call(&self, expr: Val, fn_name: &str,
                          heap: &Heap, syms: &SymbolTable) -> bool {
        if !heap.is_pair(expr) { return false; }
        let head = heap.car(expr);
        let rest = heap.cdr(expr);
        if !heap.is_symbol(head) { return false; }
        let name = syms.symbol_name(head).unwrap_or("");
        match name {
            "if" => {
                let conseq = heap.car(heap.cdr(rest));
                let alt_list = heap.cdr(heap.cdr(rest));
                let has_alt = heap.is_pair(alt_list);
                self.has_self_tail_call(conseq, fn_name, heap, syms)
                    || (has_alt && self.has_self_tail_call(heap.car(alt_list), fn_name, heap, syms))
            }
            "begin" => {
                self.has_self_tail_call_in_begin(rest, fn_name, heap, syms)
            }
            "let" | "let*" | "letrec" => {
                // Named let: (let name ((v i) ...) body...)
                // The body is after the bindings, which is after the name.
                let first = heap.car(rest);
                let body = if name == "let" && heap.is_symbol(first) {
                    // named let — skip name and bindings
                    heap.cdr(heap.cdr(rest))
                } else {
                    heap.cdr(rest)
                };
                self.has_self_tail_call_in_begin(body, fn_name, heap, syms)
            }
            "cond" => {
                let mut clauses = rest;
                while heap.is_pair(clauses) {
                    let clause = heap.car(clauses);
                    let body = heap.cdr(clause);
                    if self.has_self_tail_call_in_begin(body, fn_name, heap, syms) {
                        return true;
                    }
                    clauses = heap.cdr(clauses);
                }
                false
            }
            _ => name == fn_name,
        }
    }

    /// Check if the last expression in a begin-style list has a self-tail-call.
    fn has_self_tail_call_in_begin(&self, mut list: Val, fn_name: &str,
                                    heap: &Heap, syms: &SymbolTable) -> bool {
        let mut last = Val::NIL;
        while heap.is_pair(list) {
            last = heap.car(list);
            list = heap.cdr(list);
        }
        self.has_self_tail_call(last, fn_name, heap, syms)
    }

    /// When inside a TCO loop, wrap a value expression with `return`.
    /// Otherwise, return as-is (implicit return from function).
    fn tco_return(&self, pad: &str, expr_code: &str) -> String {
        if self.tco.borrow().is_some() {
            format!("{pad}return {expr_code}\n")
        } else {
            format!("{pad}{expr_code}\n")
        }
    }

    // ── Closure support helpers ────────────────────────────────────

    /// Check if a name is a callable builtin (can be used as a first-class value).
    fn is_callable_builtin(name: &str) -> bool {
        matches!(name,
            "+" | "-" | "*" | "/" | "=" | "<" | ">" | "<=" | ">=" |
            "cons" | "car" | "cdr" | "null?" | "pair?" | "number?" | "integer?" |
            "zero?" | "positive?" | "negative?" | "even?" | "odd?" | "not" |
            "eq?" | "eqv?" | "equal?" | "boolean?" | "procedure?" |
            "abs" | "max" | "min" | "expt" | "gcd" | "quotient" | "remainder" | "modulo" |
            "set-car!" | "set-cdr!" | "length" | "append" | "reverse" |
            "list-ref" | "list-tail" | "list" | "map" | "for-each" |
            "display" | "newline" | "write" | "write-char" | "apply" | "error" |
            "exact?" | "inexact?" | "char?" | "string?" | "vector?" | "symbol?" |
            "char->integer" | "integer->char" | "number->string" | "string->number" |
            "string-length" | "string-ref" | "string-append" |
            "make-vector" | "vector-length" | "vector-ref" | "vector-set!" |
            "lcm" | "raise" | "values" | "call-with-values" |
            "error-object?" | "error-object-message" | "error-object-irritants"
        )
    }

    /// Get or create a builtin closure ID for a builtin used as a value.
    fn get_or_create_builtin_closure(&self, name: &str) -> usize {
        if let Some(&id) = self.builtin_closures.borrow().get(name) {
            return id;
        }
        let id = self.next_lambda_id.get();
        self.next_lambda_id.set(id + 1);
        self.builtin_closures.borrow_mut().insert(name.to_string(), id);
        id
    }

    /// Check if a name is a global variable (accessible as static).
    fn is_global(&self, name: &str) -> bool {
        self.globals.iter().any(|(n, _)| n == name)
    }

    /// Check if a known top-level function is variadic (has rest param).
    fn is_variadic_function(&self, name: &str) -> bool {
        self.functions.iter().any(|f| f.name == name && f.rest_param.is_some())
    }

    /// Check if a name is a known top-level function (including record type functions).
    fn is_known_function(&self, name: &str) -> bool {
        self.functions.iter().any(|f| f.name == name)
            || self.record_types.iter().any(|rt| {
                rt.constructor_name == name
                    || rt.predicate_name == name
                    || rt.accessors.iter().any(|(_, n)| n == name)
                    || rt.mutators.iter().any(|(_, n)| n == name)
            })
    }

    /// Get the closure ID for a known top-level function, if any.
    fn function_closure_id(&self, name: &str) -> Option<usize> {
        self.functions.iter().position(|f| f.name == name)
    }

    /// Check if a name is a compiler builtin or special form (not a user variable).
    fn is_builtin_or_special(name: &str) -> bool {
        matches!(name,
            "+" | "-" | "*" | "/" | "=" | "<" | ">" | "<=" | ">=" |
            "cons" | "car" | "cdr" | "null?" | "pair?" | "number?" | "integer?" |
            "zero?" | "positive?" | "negative?" | "even?" | "odd?" | "not" |
            "eq?" | "eqv?" | "equal?" | "boolean?" | "procedure?" |
            "abs" | "max" | "min" | "expt" | "gcd" | "quotient" | "remainder" | "modulo" |
            "set-car!" | "set-cdr!" | "length" | "append" | "reverse" |
            "list-ref" | "list-tail" | "list" | "map" | "for-each" |
            "display" | "newline" | "write" | "write-char" | "apply" | "error" |
            "if" | "let" | "let*" | "letrec" | "begin" | "cond" | "case" |
            "and" | "or" | "do" | "define" | "define-record-type" |
            "define-library" | "import" | "export" | "set!" |
            "lambda" | "case-lambda" | "quote" |
            "quasiquote" | "unquote" | "unquote-splicing" | "else" |
            "dot" | "tau" | "type-valid?" | "strict-mode" | "permissive-mode" |
            "exact?" | "inexact?" | "char?" | "string?" | "vector?" | "symbol?" |
            "char->integer" | "integer->char" | "number->string" | "string->number" |
            "string-length" | "string-ref" | "string-append" |
            "make-vector" | "make-string" | "vector-length" | "vector-ref" | "vector-set!" |
            "symbol->string" | "string->symbol" | "eof-object?" |
            "char=?" | "char<?" | "char>?" | "char<=?" | "char>=?" |
            "char-ci=?" | "char-ci<?" | "char-ci>?" | "char-ci<=?" | "char-ci>=?" |
            "char-alphabetic?" | "char-numeric?" | "char-whitespace?" |
            "char-upper-case?" | "char-lower-case?" | "char-upcase" | "char-downcase" |
            "string-ci=?" | "string-ci<?" | "string-ci>?" | "string-ci<=?" | "string-ci>=?" |
            "string=?" | "string<?" | "string>?" | "string<=?" | "string>=?" |
            "string-set!" | "substring" |
            "call-with-current-continuation" | "call/cc" | "force" | "lcm" |
            "read" |
            "open-input-file" | "open-output-file" | "close-port" |
            "read-char" | "peek-char" | "read-line" |
            "current-input-port" | "current-output-port" | "current-error-port" |
            "port?" | "input-port?" | "output-port?" |
            "eof-object" | "eof-object?" |
            "write-string" | "display-string" |
            "values" | "call-with-values" |
            "raise" | "error-object?" | "error-object-message" | "error-object-irritants" |
            "guard" | "with-exception-handler" |
            // Algebra constants (global Val consts in generated code)
            "TOP" | "BOT" | "Q" | "E" | "CAR" | "CDR" | "CONS" | "RHO" |
            "APPLY" | "CC" | "TAU" | "Y" |
            "T_PAIR" | "T_SYM" | "T_CLS" | "T_STR" | "T_VEC" | "T_CHAR" |
            "T_CONT" | "T_PORT" | "TRUE" | "EOF" | "VOID"
        )
    }

    fn walk_free_vars(&self, expr: Val, heap: &Heap, syms: &SymbolTable,
                      bound: &HashSet<String>,
                      fv: &mut Vec<String>, seen: &mut HashSet<String>) {
        if expr.is_fixnum() || expr == Val::NIL { return; }
        let tag = heap.tag(expr);
        if tag == table::T_SYM {
            let name = syms.symbol_name(expr).unwrap_or("").to_string();
            if !name.is_empty() && !bound.contains(&name)
                && !Self::is_builtin_or_special(&name)
                && !self.is_known_function(&name)
                && !self.is_global(&name)
                && !seen.contains(&name)
            {
                seen.insert(name.clone());
                fv.push(name);
            }
            return;
        }
        if tag != table::T_PAIR { return; }

        let head = heap.car(expr);
        let rest = heap.cdr(expr);

        if heap.is_symbol(head) {
            let name = syms.symbol_name(head).unwrap_or("");
            match name {
                "quote" => { /* don't descend */ }
                "lambda" => {
                    let params_list = heap.car(rest);
                    let body_exprs = heap.cdr(rest);
                    let mut new_bound = bound.clone();
                    if heap.is_symbol(params_list) {
                        // (lambda args body) — bare symbol
                        if let Some(pname) = syms.symbol_name(params_list) {
                            new_bound.insert(pname.to_string());
                        }
                    } else {
                        let mut p = params_list;
                        while heap.is_pair(p) {
                            if let Some(pname) = syms.symbol_name(heap.car(p)) {
                                new_bound.insert(pname.to_string());
                            }
                            p = heap.cdr(p);
                        }
                        // Rest param in dotted tail
                        if heap.is_symbol(p) {
                            if let Some(pname) = syms.symbol_name(p) {
                                new_bound.insert(pname.to_string());
                            }
                        }
                    }
                    self.walk_free_vars_list(body_exprs, heap, syms, &new_bound, fv, seen);
                }
                "case-lambda" => {
                    // Walk free vars in each clause: ((params...) body...)
                    let mut clauses = rest;
                    while heap.is_pair(clauses) {
                        let clause = heap.car(clauses);
                        let params_list = heap.car(clause);
                        let body_exprs = heap.cdr(clause);
                        let mut new_bound = bound.clone();
                        let mut p = params_list;
                        while heap.is_pair(p) {
                            if let Some(pname) = syms.symbol_name(heap.car(p)) {
                                new_bound.insert(pname.to_string());
                            }
                            p = heap.cdr(p);
                        }
                        // Rest param in dotted tail
                        if heap.is_symbol(p) {
                            if let Some(pname) = syms.symbol_name(p) {
                                new_bound.insert(pname.to_string());
                            }
                        }
                        self.walk_free_vars_list(body_exprs, heap, syms, &new_bound, fv, seen);
                        clauses = heap.cdr(clauses);
                    }
                }
                "let" => {
                    let first = heap.car(rest);
                    if heap.is_symbol(first) {
                        // Named let: (let name ((var init) ...) body...)
                        let loop_name = syms.symbol_name(first).unwrap_or("_").to_string();
                        let bindings = heap.car(heap.cdr(rest));
                        let body_exprs = heap.cdr(heap.cdr(rest));
                        let mut new_bound = bound.clone();
                        new_bound.insert(loop_name);
                        let mut b = bindings;
                        while heap.is_pair(b) {
                            let binding = heap.car(b);
                            let init = heap.car(heap.cdr(binding));
                            self.walk_free_vars(init, heap, syms, bound, fv, seen);
                            if let Some(vname) = syms.symbol_name(heap.car(binding)) {
                                new_bound.insert(vname.to_string());
                            }
                            b = heap.cdr(b);
                        }
                        self.walk_free_vars_list(body_exprs, heap, syms, &new_bound, fv, seen);
                    } else {
                        // Regular let
                        let bindings = first;
                        let body_exprs = heap.cdr(rest);
                        let mut new_bound = bound.clone();
                        let mut b = bindings;
                        while heap.is_pair(b) {
                            let binding = heap.car(b);
                            let init = heap.car(heap.cdr(binding));
                            self.walk_free_vars(init, heap, syms, bound, fv, seen);
                            if let Some(vname) = syms.symbol_name(heap.car(binding)) {
                                new_bound.insert(vname.to_string());
                            }
                            b = heap.cdr(b);
                        }
                        self.walk_free_vars_list(body_exprs, heap, syms, &new_bound, fv, seen);
                    }
                }
                "let*" => {
                    let bindings = heap.car(rest);
                    let body_exprs = heap.cdr(rest);
                    let mut new_bound = bound.clone();
                    let mut b = bindings;
                    while heap.is_pair(b) {
                        let binding = heap.car(b);
                        let init = heap.car(heap.cdr(binding));
                        self.walk_free_vars(init, heap, syms, &new_bound, fv, seen);
                        if let Some(vname) = syms.symbol_name(heap.car(binding)) {
                            new_bound.insert(vname.to_string());
                        }
                        b = heap.cdr(b);
                    }
                    self.walk_free_vars_list(body_exprs, heap, syms, &new_bound, fv, seen);
                }
                "letrec" => {
                    let bindings = heap.car(rest);
                    let body_exprs = heap.cdr(rest);
                    let mut new_bound = bound.clone();
                    let mut b = bindings;
                    while heap.is_pair(b) {
                        if let Some(vname) = syms.symbol_name(heap.car(heap.car(b))) {
                            new_bound.insert(vname.to_string());
                        }
                        b = heap.cdr(b);
                    }
                    b = bindings;
                    while heap.is_pair(b) {
                        let init = heap.car(heap.cdr(heap.car(b)));
                        self.walk_free_vars(init, heap, syms, &new_bound, fv, seen);
                        b = heap.cdr(b);
                    }
                    self.walk_free_vars_list(body_exprs, heap, syms, &new_bound, fv, seen);
                }
                "set!" => {
                    // (set! var expr) — var reference + walk expr
                    let var = heap.car(rest);
                    if heap.is_symbol(var) {
                        self.walk_free_vars(var, heap, syms, bound, fv, seen);
                    }
                    self.walk_free_vars(heap.car(heap.cdr(rest)), heap, syms, bound, fv, seen);
                }
                "define" => {
                    // skip defines inside lambda bodies
                    self.walk_free_vars_list(heap.cdr(rest), heap, syms, bound, fv, seen);
                }
                "if" | "begin" | "and" | "or" | "cond" | "case" | "do" => {
                    self.walk_free_vars_list(rest, heap, syms, bound, fv, seen);
                }
                _ => {
                    // Function call: head (if not builtin/known) + all args
                    if !Self::is_builtin_or_special(name) && !self.is_known_function(name)
                        && !bound.contains(name) && !seen.contains(name) {
                        seen.insert(name.to_string());
                        fv.push(name.to_string());
                    }
                    self.walk_free_vars_list(rest, heap, syms, bound, fv, seen);
                }
            }
        } else {
            // Non-symbol head
            self.walk_free_vars(head, heap, syms, bound, fv, seen);
            self.walk_free_vars_list(rest, heap, syms, bound, fv, seen);
        }
    }

    fn walk_free_vars_list(&self, mut list: Val, heap: &Heap, syms: &SymbolTable,
                           bound: &HashSet<String>,
                           fv: &mut Vec<String>, seen: &mut HashSet<String>) {
        while heap.is_pair(list) {
            self.walk_free_vars(heap.car(list), heap, syms, bound, fv, seen);
            list = heap.cdr(list);
        }
    }

    /// Handle a lambda expression — lift it and return make_closure code.
    fn compile_lambda(&self, rest: Val, heap: &Heap, syms: &SymbolTable) -> String {
        let params_list = heap.car(rest);
        let body_list = heap.cdr(rest);

        // Collect params — handle bare symbol (lambda args body) and dotted (lambda (x . rest) body)
        let mut params = Vec::new();
        let mut rest_param = None;
        if heap.is_symbol(params_list) {
            // (lambda args body) — all args collected into a list
            rest_param = syms.symbol_name(params_list).map(|s| s.to_string());
        } else {
            let mut p = params_list;
            while heap.is_pair(p) {
                if let Some(pname) = syms.symbol_name(heap.car(p)) {
                    params.push(pname.to_string());
                }
                p = heap.cdr(p);
            }
            // Check for rest param (dotted tail)
            if heap.is_symbol(p) {
                rest_param = syms.symbol_name(p).map(|s| s.to_string());
            }
        }

        // Analyze free variables
        let mut bound: HashSet<String> = params.iter().cloned().collect();
        if let Some(ref rp) = rest_param { bound.insert(rp.clone()); }
        // Also add global names to bound so they aren't captured
        // (globals are available to top-level functions but NOT to lifted lambdas,
        //  so we actually DO want to capture them)
        let fvs = self.collect_free_vars_list(body_list, heap, syms, &bound);

        // Assign ID
        let id = self.next_lambda_id.get();
        self.next_lambda_id.set(id + 1);

        // Store lifted lambda
        self.lifted.borrow_mut().push(LiftedLambda {
            id,
            params,
            rest_param,
            free_vars: fvs.clone(),
            body_list,
            case_clauses: None,
        });

        // Emit closure creation
        if fvs.is_empty() {
            format!("make_closure({id}, Val::NIL)")
        } else {
            let mut env = "Val::NIL".to_string();
            for fv in fvs.iter().rev() {
                let rv = rust_ident(fv);
                env = format!("cons({rv}, {env})");
            }
            format!("make_closure({id}, {env})")
        }
    }

    /// Handle a case-lambda expression — lift it and return make_closure code.
    fn compile_case_lambda(&self, rest: Val, heap: &Heap, syms: &SymbolTable) -> String {
        // Collect all clauses: ((params...) body...)
        let mut clauses = Vec::new();
        let mut c = rest;
        while heap.is_pair(c) {
            let clause = heap.car(c);
            let params_list = heap.car(clause);
            let body_list = heap.cdr(clause);
            let mut params = Vec::new();
            let mut clause_rest = None;
            let mut p = params_list;
            while heap.is_pair(p) {
                if let Some(pname) = syms.symbol_name(heap.car(p)) {
                    params.push(pname.to_string());
                }
                p = heap.cdr(p);
            }
            if heap.is_symbol(p) {
                clause_rest = syms.symbol_name(p).map(|s| s.to_string());
            }
            clauses.push(CaseClause { params, rest_param: clause_rest, body_list });
            c = heap.cdr(c);
        }

        // Collect free vars across all clauses
        let mut all_bound = HashSet::new();
        for clause in &clauses {
            for p in &clause.params {
                all_bound.insert(p.clone());
            }
        }
        // Collect free vars relative to each clause's params
        let mut fv = Vec::new();
        let mut seen = HashSet::new();
        for clause in &clauses {
            let mut clause_bound: HashSet<String> = clause.params.iter().cloned().collect();
            if let Some(ref rp) = clause.rest_param { clause_bound.insert(rp.clone()); }
            self.walk_free_vars_list(clause.body_list, heap, syms, &clause_bound, &mut fv, &mut seen);
        }
        // Filter out builtins and known functions
        let fvs: Vec<String> = fv.into_iter().collect();

        // Assign ID
        let id = self.next_lambda_id.get();
        self.next_lambda_id.set(id + 1);

        // Use first clause's params as the nominal params (for dispatch table arity)
        let nominal_params = if clauses.is_empty() { vec![] } else { clauses[0].params.clone() };

        // Store lifted lambda with case_clauses
        self.lifted.borrow_mut().push(LiftedLambda {
            id,
            params: nominal_params,
            rest_param: None,
            free_vars: fvs.clone(),
            body_list: Val::NIL, // not used for case-lambda
            case_clauses: Some(clauses),
        });

        // Emit closure creation
        if fvs.is_empty() {
            format!("make_closure({id}, Val::NIL)")
        } else {
            let mut env = "Val::NIL".to_string();
            for fv in fvs.iter().rev() {
                let rv = rust_ident(fv);
                env = format!("cons({rv}, {env})");
            }
            format!("make_closure({id}, {env})")
        }
    }

    fn collect_free_vars_list(&self, list: Val, heap: &Heap, syms: &SymbolTable,
                              bound: &HashSet<String>) -> Vec<String> {
        let mut fv = Vec::new();
        let mut seen = HashSet::new();
        self.walk_free_vars_list(list, heap, syms, bound, &mut fv, &mut seen);
        fv
    }

    /// Emit free variable extraction code from __env.
    fn emit_env_extraction(free_vars: &[String]) -> String {
        let mut out = String::new();
        for (i, fv) in free_vars.iter().enumerate() {
            let rv = rust_ident(fv);
            let access = if i == 0 {
                "car(__env)".to_string()
            } else {
                let mut s = "__env".to_string();
                for _ in 0..i {
                    s = format!("cdr({s})");
                }
                format!("car({s})")
            };
            out.push_str(&format!("    let {rv} = {access};\n"));
        }
        out
    }

    /// Emit a lifted lambda function definition.
    fn emit_lifted_lambda(&self, lambda: &LiftedLambda, heap: &Heap, syms: &SymbolTable) -> String {
        let lname = format!("__lambda_{}", lambda.id);

        // Case-lambda: takes args as a slice, dispatches on count
        if let Some(ref clauses) = lambda.case_clauses {
            let mut out = format!("fn {lname}(__env: Val, args: &[Val]) -> Val {{\n");
            out.push_str(&Self::emit_env_extraction(&lambda.free_vars));
            out.push_str("    match args.len() {\n");
            for clause in clauses {
                let arity = clause.params.len();
                if clause.rest_param.is_some() {
                    out.push_str(&format!("        __n if __n >= {arity} => {{\n"));
                } else {
                    out.push_str(&format!("        {arity} => {{\n"));
                }
                for (i, p) in clause.params.iter().enumerate() {
                    out.push_str(&format!("            let {} = args[{i}];\n", rust_ident(p)));
                }
                if let Some(ref rp) = clause.rest_param {
                    let rn = rust_ident(rp);
                    out.push_str(&format!("            let {rn} = {{ let mut __r = Val::NIL; let mut __i = args.len(); while __i > {arity} {{ __i -= 1; __r = cons(args[__i], __r); }} __r }};\n"));
                }
                out.push_str(&self.emit_begin(clause.body_list, heap, syms, 3));
                out.push_str("        }\n");
            }
            out.push_str("        _ => Val::NIL,\n");
            out.push_str("    }\n");
            out.push_str("}\n\n");
            return out;
        }

        // Variadic lambda: takes args as a slice
        if lambda.rest_param.is_some() {
            let mut out = format!("fn {lname}(__env: Val, args: &[Val]) -> Val {{\n");
            out.push_str(&Self::emit_env_extraction(&lambda.free_vars));
            for (i, p) in lambda.params.iter().enumerate() {
                out.push_str(&format!("    let {} = args[{i}];\n", rust_ident(p)));
            }
            let rest_name = rust_ident(lambda.rest_param.as_ref().unwrap());
            let n_fixed = lambda.params.len();
            out.push_str(&format!("    let {rest_name} = {{ let mut __r = Val::NIL; let mut __i = args.len(); while __i > {n_fixed} {{ __i -= 1; __r = cons(args[__i], __r); }} __r }};\n"));
            out.push_str(&self.emit_begin(lambda.body_list, heap, syms, 1));
            out.push_str("}\n\n");
            return out;
        }

        // Regular lambda
        let mut rparams = vec!["__env: Val".to_string()];
        for p in &lambda.params {
            rparams.push(format!("{}: Val", rust_ident(p)));
        }
        let params_str = rparams.join(", ");

        let mut out = format!("fn {lname}({params_str}) -> Val {{\n");
        out.push_str(&Self::emit_env_extraction(&lambda.free_vars));

        // Emit body
        out.push_str(&self.emit_begin(lambda.body_list, heap, syms, 1));
        out.push_str("}\n\n");
        out
    }

    /// Generate the dispatch_closure function.
    /// Emit wrapper functions for builtins used as first-class values.
    fn emit_builtin_wrappers(&self) -> String {
        let closures = self.builtin_closures.borrow();
        if closures.is_empty() { return String::new(); }
        let mut out = String::from("// Builtin closure wrappers\n");
        for (name, id) in closures.iter() {
            let fname = format!("__builtin_{id}");
            out.push_str(&format!("fn {fname}(__env: Val, args: &[Val]) -> Val {{\n"));
            out.push_str(&Self::emit_builtin_wrapper_body(name));
            out.push_str("}\n\n");
        }
        out
    }

    /// Generate the body of a builtin wrapper function.
    fn emit_builtin_wrapper_body(name: &str) -> String {
                let body = match name {
                    "+" => "    let mut __acc = 0i64; for __a in args { __acc += __a.as_fixnum().unwrap(); } Val::fixnum(__acc)\n",
                    "-" => "    if args.len() == 1 { Val::fixnum(-args[0].as_fixnum().unwrap()) } else { Val::fixnum(args[0].as_fixnum().unwrap() - args[1].as_fixnum().unwrap()) }\n",
                    "*" => "    let mut __acc = 1i64; for __a in args { __acc *= __a.as_fixnum().unwrap(); } Val::fixnum(__acc)\n",
                    "/" | "quotient" => "    Val::fixnum(args[0].as_fixnum().unwrap() / args[1].as_fixnum().unwrap())\n",
                    "remainder" | "modulo" => "    Val::fixnum(args[0].as_fixnum().unwrap() % args[1].as_fixnum().unwrap())\n",
                    "=" => "    bool_to_val(args[0].as_fixnum().unwrap() == args[1].as_fixnum().unwrap())\n",
                    "<" => "    bool_to_val(args[0].as_fixnum().unwrap() < args[1].as_fixnum().unwrap())\n",
                    ">" => "    bool_to_val(args[0].as_fixnum().unwrap() > args[1].as_fixnum().unwrap())\n",
                    "<=" => "    bool_to_val(args[0].as_fixnum().unwrap() <= args[1].as_fixnum().unwrap())\n",
                    ">=" => "    bool_to_val(args[0].as_fixnum().unwrap() >= args[1].as_fixnum().unwrap())\n",
                    "cons" => "    cons(args[0], args[1])\n",
                    "car" => "    car(args[0])\n",
                    "cdr" => "    cdr(args[0])\n",
                    "null?" => "    bool_to_val(args[0] == Val::NIL)\n",
                    "pair?" => "    bool_to_val(args[0] != Val::NIL && !args[0].is_fixnum())\n",
                    "number?" | "integer?" => "    bool_to_val(args[0].is_fixnum())\n",
                    "zero?" => "    bool_to_val(args[0].as_fixnum() == Some(0))\n",
                    "positive?" => "    bool_to_val(args[0].as_fixnum().map_or(false, |n| n > 0))\n",
                    "negative?" => "    bool_to_val(args[0].as_fixnum().map_or(false, |n| n < 0))\n",
                    "even?" => "    bool_to_val(args[0].as_fixnum().unwrap() % 2 == 0)\n",
                    "odd?" => "    bool_to_val(args[0].as_fixnum().unwrap() % 2 != 0)\n",
                    "not" => "    bool_to_val(!is_true(args[0]))\n",
                    "eq?" | "eqv?" => "    bool_to_val(args[0] == args[1])\n",
                    "equal?" => "    bool_to_val(scheme_equal(args[0], args[1]))\n",
                    "boolean?" => "    bool_to_val(args[0] == TRUE_VAL || args[0] == FALSE_VAL)\n",
                    "procedure?" => "    bool_to_val(!args[0].is_fixnum() && args[0] != Val::NIL && unsafe { HEAP[args[0].as_rib()].tag == TAG_CLS })\n",
                    "abs" => "    Val::fixnum(args[0].as_fixnum().unwrap().abs())\n",
                    "max" => "    Val::fixnum(std::cmp::max(args[0].as_fixnum().unwrap(), args[1].as_fixnum().unwrap()))\n",
                    "min" => "    Val::fixnum(std::cmp::min(args[0].as_fixnum().unwrap(), args[1].as_fixnum().unwrap()))\n",
                    "length" => "    { let mut __l = args[0]; let mut __n = 0i64; while __l != Val::NIL && !__l.is_fixnum() { __n += 1; __l = cdr(__l); } Val::fixnum(__n) }\n",
                    "append" => "    append(args[0], args[1])\n",
                    "reverse" => "    { let mut __l = args[0]; let mut __r = Val::NIL; while __l != Val::NIL && !__l.is_fixnum() { __r = cons(car(__l), __r); __l = cdr(__l); } __r }\n",
                    "list" => "    { let mut __r = Val::NIL; let mut __i = args.len(); while __i > 0 { __i -= 1; __r = cons(args[__i], __r); } __r }\n",
                    "display" => "    { display(args[0]); Val::NIL }\n",
                    "newline" => "    { println!(); Val::NIL }\n",
                    "write" => "    { scheme_write(args[0]); Val::NIL }\n",
                    "map" => "    scheme_map(args[0], args[1])\n",
                    "for-each" => "    { scheme_for_each(args[0], args[1]); Val::NIL }\n",
                    "apply" => "    scheme_apply(args[0], &args[1..])\n",
                    "set-car!" => "    { set_car(args[0], args[1]); Val::NIL }\n",
                    "set-cdr!" => "    { set_cdr(args[0], args[1]); Val::NIL }\n",
                    "list-ref" => "    list_ref(args[0], args[1].as_fixnum().unwrap())\n",
                    "list-tail" => "    list_tail(args[0], args[1].as_fixnum().unwrap())\n",
                    "string-length" => "    string_length(args[0])\n",
                    "string-ref" => "    string_ref(args[0], args[1])\n",
                    "string-append" => "    string_append(args[0], args[1])\n",
                    "make-vector" => "    make_vector_fill(args[0].as_fixnum().unwrap(), if args.len() > 1 { args[1] } else { Val::fixnum(0) })\n",
                    "vector-length" => "    vector_length(args[0])\n",
                    "vector-ref" => "    vector_ref(args[0], args[1].as_fixnum().unwrap())\n",
                    "vector-set!" => "    { vector_set(args[0], args[1].as_fixnum().unwrap(), args[2]); Val::NIL }\n",
                    "vector?" => "    bool_to_val(is_vector(args[0]))\n",
                    "char?" => "    bool_to_val(is_char(args[0]))\n",
                    "string?" => "    bool_to_val(is_string(args[0]))\n",
                    "exact?" => "    bool_to_val(args[0].is_fixnum())\n",
                    "inexact?" => "    bool_to_val(!args[0].is_fixnum())\n",
                    "expt" => "    Val::fixnum(args[0].as_fixnum().unwrap().pow(args[1].as_fixnum().unwrap() as u32))\n",
                    "char->integer" => "    char_to_integer(args[0])\n",
                    "integer->char" => "    make_char(args[0].as_fixnum().unwrap())\n",
                    "number->string" => "    number_to_string(args[0])\n",
                    "string->number" => "    string_to_number(args[0])\n",
                    "values" => "    if args.len() == 1 { args[0] } else { let mut __l = Val::NIL; let mut __i = args.len(); while __i > 0 { __i -= 1; __l = cons(args[__i], __l); } make_values(__l, args.len() as i64) }\n",
                    "call-with-values" => "    call_with_values(args[0], args[1])\n",
                    "error" => "    { let mut __irr = Val::NIL; let mut __i = args.len(); while __i > 1 { __i -= 1; __irr = cons(args[__i], __irr); } scheme_raise(make_error(args[0], __irr)) }\n",
                    "raise" => "    scheme_raise(args[0])\n",
                    "error-object?" => "    bool_to_val(is_error_object(args[0]))\n",
                    "error-object-message" => "    car(args[0])\n",
                    "error-object-irritants" => "    cdr(args[0])\n",
                    "gcd" => "    { let (mut a, mut b) = (args[0].as_fixnum().unwrap().abs(), args[1].as_fixnum().unwrap().abs()); while b != 0 { let t = b; b = a % b; a = t; } Val::fixnum(a) }\n",
                    "lcm" => "    { let (a, b) = (args[0].as_fixnum().unwrap().abs(), args[1].as_fixnum().unwrap().abs()); if a == 0 || b == 0 { Val::fixnum(0) } else { let (mut x, mut y) = (a, b); while y != 0 { let t = y; y = x % y; x = t; } Val::fixnum(a / x * b) } }\n",
                    "write-char" => "    { let __cp = if is_char(args[0]) { car(args[0]).as_fixnum().unwrap_or(0) } else { args[0].as_fixnum().unwrap_or(0) }; print!(\"{}\", __cp as u8 as char); Val::NIL }\n",
                    _ => "    Val::NIL\n",
                };
                body.to_string()
    }

    fn emit_dispatch(&self, _heap: &Heap, _syms: &SymbolTable) -> String {
        let mut out = String::new();
        out.push_str("fn dispatch_closure(closure: Val, args: &[Val]) -> Val {\n");
        out.push_str("    let code_id = car(closure).as_fixnum().unwrap();\n");
        out.push_str("    let __env = cdr(closure);\n");
        out.push_str("    match code_id {\n");

        // Top-level functions (IDs 0..N-1)
        for (i, func) in self.functions.iter().enumerate() {
            let fname = rust_ident(&func.name);
            if func.rest_param.is_some() {
                // Variadic: pass args slice
                out.push_str(&format!("        {i} => {fname}(args),\n"));
            } else {
                let args: Vec<String> = (0..func.params.len())
                    .map(|j| format!("args[{j}]"))
                    .collect();
                let args_str = args.join(", ");
                out.push_str(&format!("        {i} => {fname}({args_str}),\n"));
            }
        }

        // Lifted lambdas (IDs N..)
        for lambda in self.lifted.borrow().iter() {
            let lname = format!("__lambda_{}", lambda.id);
            if lambda.case_clauses.is_some() || lambda.rest_param.is_some() {
                // Case-lambda or variadic: pass args slice directly
                out.push_str(&format!("        {} => {lname}(__env, args),\n", lambda.id));
            } else {
                let mut args = vec!["__env".to_string()];
                for j in 0..lambda.params.len() {
                    args.push(format!("args[{j}]"));
                }
                let args_str = args.join(", ");
                out.push_str(&format!("        {} => {lname}({args_str}),\n", lambda.id));
            }
        }

        // Builtin closures
        for (_, id) in self.builtin_closures.borrow().iter() {
            let fname = format!("__builtin_{id}");
            out.push_str(&format!("        {id} => {fname}(__env, args),\n"));
        }

        out.push_str("        _ => Val::NIL,\n");
        out.push_str("    }\n");
        out.push_str("}\n\n");
        out
    }

    /// Emit the compiled Rust program as a string.
    pub fn emit_rust(&self, heap: &Heap, syms: &SymbolTable) -> String {
        // Lambda IDs: top-level functions get 0..N-1, lifted lambdas start at N
        self.next_lambda_id.set(self.functions.len());

        let mut out = String::new();

        // Header
        out.push_str("// Generated by wispy-scheme compiler\n");
        out.push_str("#![allow(non_snake_case, unused_variables, unused_mut, unused_parens, dead_code)]\n\n");

        // Inline the Cayley table
        out.push_str("// 32×32 Cayley table (1KB)\n");
        out.push_str(&format!("const N: usize = {};\n", table::N));
        // u8 constants for runtime internals (heap tags)
        out.push_str(&format!("const TAG_TOP: u8 = {};\n", table::TOP));
        out.push_str(&format!("const TAG_BOT: u8 = {};\n", table::BOT));
        out.push_str(&format!("const TAG_PAIR: u8 = {};\n", table::T_PAIR));
        out.push_str(&format!("const TAG_CLS: u8 = {};\n", table::T_CLS));
        out.push_str(&format!("const TAG_STR: u8 = {};\n", table::T_STR));
        out.push_str(&format!("const TAG_CHAR: u8 = {};\n", table::T_CHAR));
        out.push_str(&format!("const TAG_VALUES: u8 = {};\n", table::T_VALUES));
        out.push_str(&format!("const TAG_ERROR: u8 = {};\n", table::T_ERROR));
        out.push_str(&format!("const TAG_RECORD: u8 = {};\n", table::T_RECORD));
        out.push_str(&format!("const TAG_VEC: u8 = {};\n", table::T_VEC));
        out.push_str(&format!("const TAG_CONT: u8 = {};\n", table::T_CONT));
        out.push_str(&format!("const TAG_PORT: u8 = {};\n", table::T_PORT));
        out.push_str(&format!("const TAG_EOF: u8 = {};\n", table::EOF));
        out.push_str("\n");

        // Inline the table data
        out.push_str("static CAYLEY: [[u8; 32]; 32] = ");
        out.push_str(&self.emit_table_literal());
        out.push_str(";\n\n");

        // Value type and heap
        out.push_str(RUNTIME_PRELUDE);
        out.push_str("\n");

        // Algebra element constants (Val) — accessible from compiled Scheme code
        let elements: &[(&str, u8)] = &[
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
        out.push_str("// Algebra element constants\n");
        for (name, val) in elements {
            out.push_str(&format!("const {name}: Val = Val::fixnum({} as i64);\n", *val));
        }
        out.push_str("\n");

        // ── Code generation (may discover lambdas) ─────────────────

        // Collect function bodies (this triggers lambda lifting)
        let mut func_code = String::new();
        for func in &self.functions {
            let rname = rust_ident(&func.name);
            // Track current function's parameters so emit_expr_inline doesn't use
            // the direct-call optimization for known functions that are shadowed by local params.
            {
                let mut cp = self.current_params.borrow_mut();
                cp.clear();
                cp.extend(func.params.iter().cloned());
                if let Some(ref rp) = func.rest_param { cp.insert(rp.clone()); }
            }

            if func.rest_param.is_some() {
                // Variadic function: takes args slice
                func_code.push_str(&format!("fn {rname}(args: &[Val]) -> Val {{\n"));
                // Extract fixed params
                for (i, p) in func.params.iter().enumerate() {
                    let rp = rust_ident(p);
                    let mutk = if self.is_set_target(p) { "mut " } else { "" };
                    func_code.push_str(&format!("    let {mutk}{rp} = args[{i}];\n"));
                }
                // Collect rest args into a list
                let rest_name = rust_ident(func.rest_param.as_ref().unwrap());
                let n_fixed = func.params.len();
                let mutk = if self.is_set_target(func.rest_param.as_ref().unwrap()) { "mut " } else { "" };
                func_code.push_str(&format!("    let {mutk}{rest_name} = {{ let mut __r = Val::NIL; let mut __i = args.len(); while __i > {n_fixed} {{ __i -= 1; __r = cons(args[__i], __r); }} __r }};\n"));
                let body_code = self.emit_expr(func.body, heap, syms, 1);
                func_code.push_str(&body_code);
                func_code.push_str("}\n\n");
            } else {
            let needs_tco = self.has_self_tail_call(func.body, &func.name, heap, syms);

            if needs_tco {
                // Emit with mut params and loop wrapper
                let rparams: Vec<String> = func.params.iter()
                    .map(|p| format!("mut {}: Val", rust_ident(p)))
                    .collect();
                let params_str = rparams.join(", ");
                func_code.push_str(&format!("fn {rname}({params_str}) -> Val {{\n"));
                func_code.push_str("    loop {\n");
                // Set TCO context
                *self.tco.borrow_mut() = Some(TcoContext {
                    fn_name: func.name.clone(),
                    params: func.params.clone(),
                });
                let body_code = self.emit_expr(func.body, heap, syms, 2);
                func_code.push_str(&body_code);
                *self.tco.borrow_mut() = None;
                func_code.push_str("    }\n");
                func_code.push_str("}\n\n");
            } else {
                let rparams: Vec<String> = func.params.iter()
                    .map(|p| {
                        let mutk = if self.is_set_target(p) { "mut " } else { "" };
                        format!("{mutk}{}: Val", rust_ident(p))
                    })
                    .collect();
                let params_str = rparams.join(", ");
                func_code.push_str(&format!("fn {rname}({params_str}) -> Val {{\n"));
                let body_code = self.emit_expr(func.body, heap, syms, 1);
                func_code.push_str(&body_code);
                func_code.push_str("}\n\n");
            }
            } // end if rest_param else
        }
        self.current_params.borrow_mut().clear();

        // Emit record type functions (constructors, predicates, accessors, mutators)
        let mut record_code = String::new();
        for rt in &self.record_types {
            let _n_fields = rt.constructor_fields.len();
            // Constructor
            let cname = rust_ident(&rt.constructor_name);
            let cparams: Vec<String> = rt.constructor_fields.iter()
                .map(|f| format!("{}: Val", rust_ident(f)))
                .collect();
            record_code.push_str(&format!("fn {cname}({}) -> Val {{\n", cparams.join(", ")));
            let mut fields = "Val::NIL".to_string();
            for f in rt.constructor_fields.iter().rev() {
                fields = format!("cons({}, {fields})", rust_ident(f));
            }
            record_code.push_str(&format!("    make_record({}, {fields})\n", rt.type_id));
            record_code.push_str("}\n\n");

            // Predicate
            let pname = rust_ident(&rt.predicate_name);
            record_code.push_str(&format!("fn {pname}(v: Val) -> Val {{\n"));
            record_code.push_str(&format!("    bool_to_val(is_record_type(v, {}))\n", rt.type_id));
            record_code.push_str("}\n\n");

            // Accessors
            for (idx, accessor_name) in &rt.accessors {
                let aname = rust_ident(accessor_name);
                record_code.push_str(&format!("fn {aname}(v: Val) -> Val {{\n"));
                record_code.push_str(&format!("    record_ref(v, {idx})\n"));
                record_code.push_str("}\n\n");
            }

            // Mutators
            for (idx, mutator_name) in &rt.mutators {
                let mname = rust_ident(mutator_name);
                record_code.push_str(&format!("fn {mname}(v: Val, new_val: Val) -> Val {{\n"));
                record_code.push_str(&format!("    record_set(v, {idx}, new_val); Val::NIL\n"));
                record_code.push_str("}\n\n");
            }
        }

        // Emit globals as module-level statics (accessible from lifted lambdas)
        let mut statics_code = String::new();
        let mut globals_init_code = String::new();
        for (name, init) in &self.globals {
            let rname = rust_ident(name);
            let init_code = self.emit_expr_inline(*init, heap, syms);
            statics_code.push_str(&format!("static mut {rname}: Val = Val(0);\n"));
            globals_init_code.push_str(
                &format!("    unsafe {{ {rname} = {init_code}; }}\n"));
        }
        let mut main_code = String::new();
        for &expr in &self.main_exprs {
            let code = self.emit_expr_inline(expr, heap, syms);
            main_code.push_str(&format!("    {{ let _ = {code}; }}\n"));
        }

        // Emit lifted lambdas (fixpoint: emitting bodies may discover more)
        let mut lifted_code = String::new();
        let mut emitted = 0;
        loop {
            let lambdas_to_emit: Vec<LiftedLambda>;
            {
                let all = self.lifted.borrow();
                if emitted >= all.len() { break; }
                lambdas_to_emit = all[emitted..].to_vec();
                emitted = all.len();
            }
            for lambda in &lambdas_to_emit {
                lifted_code.push_str(&self.emit_lifted_lambda(lambda, heap, syms));
            }
        }

        // ── Assemble output ─────────────────────────────────────────

        // Global variable statics
        out.push_str(&statics_code);
        if !statics_code.is_empty() { out.push('\n'); }

        // Top-level Scheme functions
        out.push_str(&func_code);

        // Record type functions
        out.push_str(&record_code);

        // Lifted lambda functions
        out.push_str(&lifted_code);

        // Builtin closure wrappers (for builtins used as first-class values)
        out.push_str(&self.emit_builtin_wrappers());

        // dispatch_closure (must come after all functions are defined)
        out.push_str(&self.emit_dispatch(heap, syms));

        // Main
        out.push_str("fn main() {\n");
        out.push_str("    heap_init();\n");
        out.push_str(&globals_init_code);
        out.push_str("\n");
        out.push_str(&main_code);
        out.push_str("}\n");
        out
    }

    fn emit_table_literal(&self) -> String {
        let mut s = String::from("[\n");
        for i in 0..table::N {
            s.push_str("    [");
            for j in 0..table::N {
                if j > 0 { s.push_str(", "); }
                s.push_str(&format!("{}", table::CAYLEY[i][j]));
            }
            s.push_str("],\n");
        }
        s.push_str("]");
        s
    }

    /// Emit an expression in tail position (last expression in a block).
    /// When inside a TCO loop, leaf values are wrapped with `return`,
    /// and self-tail-calls are transformed to `continue`.
    fn emit_expr(&self, expr: Val, heap: &Heap, syms: &SymbolTable, indent: usize) -> String {
        let pad = "    ".repeat(indent);

        // Only control-flow forms need special handling in emit_expr.
        // Everything else delegates to emit_expr_inline + tco_return.
        if !heap.is_pair(expr) || heap.tag(expr) != table::T_PAIR {
            let code = self.emit_expr_inline(expr, heap, syms);
            return self.tco_return(&pad, &code);
        }

        let head = heap.car(expr);
        let rest = heap.cdr(expr);

        if heap.is_symbol(head) {
            let name = syms.symbol_name(head).unwrap_or("");

            match name {
                // ── Control-flow forms that propagate tail position ──
                "if" => {
                    let test = heap.car(rest);
                    let rest2 = heap.cdr(rest);
                    let conseq = heap.car(rest2);
                    let alt_list = heap.cdr(rest2);
                    let test_code = self.emit_expr_inline(test, heap, syms);
                    let t_code = self.emit_expr(conseq, heap, syms, indent + 1);
                    if heap.is_pair(alt_list) {
                        let f_code = self.emit_expr(heap.car(alt_list), heap, syms, indent + 1);
                        return format!(
                            "{pad}if is_true({test_code}) {{\n{t_code}{pad}}} else {{\n{f_code}{pad}}}\n"
                        );
                    } else {
                        return format!(
                            "{pad}if is_true({test_code}) {{\n{t_code}{pad}}} else {{\n{pad}    Val::NIL\n{pad}}}\n"
                        );
                    }
                }

                "begin" => {
                    return self.emit_begin(rest, heap, syms, indent);
                }

                "let" => {
                    let first = heap.car(rest);
                    // Named let: (let loop-name ((var init) ...) body ...)
                    if heap.is_symbol(first) {
                        let loop_name = syms.symbol_name(first).unwrap_or("_").to_string();
                        let bindings = heap.car(heap.cdr(rest));
                        let body = heap.cdr(heap.cdr(rest));

                        // Collect parameter names and init expressions
                        let mut param_names: Vec<String> = Vec::new();
                        let mut init_codes: Vec<String> = Vec::new();
                        let mut b = bindings;
                        while heap.is_pair(b) {
                            let binding = heap.car(b);
                            let var = heap.car(binding);
                            let init = heap.car(heap.cdr(binding));
                            let vname = syms.symbol_name(var).unwrap_or("_").to_string();
                            init_codes.push(self.emit_expr_inline(init, heap, syms));
                            param_names.push(vname);
                            b = heap.cdr(b);
                        }

                        let mut out = String::new();
                        out.push_str(&format!("{pad}{{\n"));
                        // Emit mutable variable declarations
                        for (i, pname) in param_names.iter().enumerate() {
                            out.push_str(&format!("{pad}    let mut {} = {};\n",
                                rust_ident(pname), init_codes[i]));
                        }
                        out.push_str(&format!("{pad}    loop {{\n"));

                        // Save previous TCO context and install named-let context
                        let prev_tco = self.tco.borrow().clone();
                        *self.tco.borrow_mut() = Some(TcoContext {
                            fn_name: loop_name,
                            params: param_names,
                        });

                        out.push_str(&self.emit_begin(body, heap, syms, indent + 2));

                        // Restore previous TCO context
                        *self.tco.borrow_mut() = prev_tco;

                        out.push_str(&format!("{pad}    }}\n"));
                        out.push_str(&format!("{pad}}}\n"));
                        return out;
                    }

                    // Regular let: (let ((var init) ...) body ...)
                    let bindings = first;
                    let body = heap.cdr(rest);
                    let mut out = String::new();
                    out.push_str(&format!("{pad}{{\n"));
                    let mut b = bindings;
                    while heap.is_pair(b) {
                        let binding = heap.car(b);
                        let var = heap.car(binding);
                        let init = heap.car(heap.cdr(binding));
                        let vname = syms.symbol_name(var).unwrap_or("_");
                        let init_code = self.emit_expr_inline(init, heap, syms);
                        let mutk = if self.is_set_target(vname) { "mut " } else { "" };
                        out.push_str(&format!("{pad}    let {mutk}{} = {};\n",
                            rust_ident(vname), init_code));
                        b = heap.cdr(b);
                    }
                    out.push_str(&self.emit_begin(body, heap, syms, indent + 1));
                    out.push_str(&format!("{pad}}}\n"));
                    return out;
                }

                "let*" => {
                    let bindings = heap.car(rest);
                    let body = heap.cdr(rest);
                    let mut out = String::new();
                    out.push_str(&format!("{pad}{{\n"));
                    let mut b = bindings;
                    while heap.is_pair(b) {
                        let binding = heap.car(b);
                        let var = heap.car(binding);
                        let init = heap.car(heap.cdr(binding));
                        let vname = syms.symbol_name(var).unwrap_or("_");
                        let init_code = self.emit_expr_inline(init, heap, syms);
                        let mutk = if self.is_set_target(vname) { "mut " } else { "" };
                        out.push_str(&format!("{pad}    let {mutk}{vn} = {init_code};\n",
                            vn = rust_ident(vname)));
                        b = heap.cdr(b);
                    }
                    out.push_str(&self.emit_begin(body, heap, syms, indent + 1));
                    out.push_str(&format!("{pad}}}\n"));
                    return out;
                }

                "letrec" => {
                    let bindings = heap.car(rest);
                    let body = heap.cdr(rest);
                    let mut out = String::new();
                    out.push_str(&format!("{pad}{{\n"));
                    // First pass: declare all as mut NIL
                    let mut b = bindings;
                    while heap.is_pair(b) {
                        let binding = heap.car(b);
                        let var = heap.car(binding);
                        let vname = syms.symbol_name(var).unwrap_or("_");
                        out.push_str(&format!("{pad}    let mut {} = Val::NIL;\n",
                            rust_ident(vname)));
                        b = heap.cdr(b);
                    }
                    // Second pass: assign
                    b = bindings;
                    while heap.is_pair(b) {
                        let binding = heap.car(b);
                        let var = heap.car(binding);
                        let init = heap.car(heap.cdr(binding));
                        let vname = syms.symbol_name(var).unwrap_or("_");
                        let init_code = self.emit_expr_inline(init, heap, syms);
                        out.push_str(&format!("{pad}    {} = {init_code};\n",
                            rust_ident(vname)));
                        b = heap.cdr(b);
                    }
                    // Third pass: patch closure envs so mutual references see final values.
                    // For each lambda binding, rebuild the env cons chain with current
                    // variable values and set_cdr the closure rib.
                    b = bindings;
                    while heap.is_pair(b) {
                        let binding = heap.car(b);
                        let var = heap.car(binding);
                        let init = heap.car(heap.cdr(binding));
                        let vname = syms.symbol_name(var).unwrap_or("_");
                        if heap.is_pair(init) {
                            let init_head = heap.car(init);
                            if heap.is_symbol(init_head) {
                                let iname = syms.symbol_name(init_head).unwrap_or("");
                                if iname == "lambda" || iname == "case-lambda" {
                                    // Find the free vars this lambda captures
                                    let params_list = heap.car(heap.cdr(init));
                                    let body_list = heap.cdr(heap.cdr(init));
                                    let mut param_bound: HashSet<String> = HashSet::new();
                                    if heap.is_symbol(params_list) {
                                        if let Some(pn) = syms.symbol_name(params_list) {
                                            param_bound.insert(pn.to_string());
                                        }
                                    } else {
                                        let mut p = params_list;
                                        while heap.is_pair(p) {
                                            if let Some(pn) = syms.symbol_name(heap.car(p)) {
                                                param_bound.insert(pn.to_string());
                                            }
                                            p = heap.cdr(p);
                                        }
                                        if heap.is_symbol(p) {
                                            if let Some(pn) = syms.symbol_name(p) {
                                                param_bound.insert(pn.to_string());
                                            }
                                        }
                                    }
                                    let fvs = self.collect_free_vars_list(body_list, heap, syms, &param_bound);
                                    if !fvs.is_empty() {
                                        let rv = rust_ident(vname);
                                        let mut env = "Val::NIL".to_string();
                                        for fv in fvs.iter().rev() {
                                            env = format!("cons({}, {env})", rust_ident(fv));
                                        }
                                        out.push_str(&format!("{pad}    set_cdr({rv}, {env});\n"));
                                    }
                                }
                            }
                        }
                        b = heap.cdr(b);
                    }
                    out.push_str(&self.emit_begin(body, heap, syms, indent + 1));
                    out.push_str(&format!("{pad}}}\n"));
                    return out;
                }

                "cond" => {
                    return self.emit_cond(rest, heap, syms, indent);
                }

                "case" => {
                    return self.emit_case(rest, heap, syms, indent);
                }

                // ── Control-flow forms that delegate back to emit_expr ──
                // (do is NOT tail-safe but doesn't need it in practice)
                "do" => {
                    return self.emit_do(rest, heap, syms, indent);
                }

                _ => {
                    // Check for self-tail-call (TCO)
                    let is_self_tail = {
                        let ctx = self.tco.borrow();
                        ctx.as_ref().map_or(false, |c| c.fn_name == name)
                    };
                    if is_self_tail {
                        let params: Vec<String> = {
                            let ctx = self.tco.borrow();
                            ctx.as_ref().unwrap().params.clone()
                        };
                        let mut args = Vec::new();
                        let mut a = rest;
                        while heap.is_pair(a) {
                            args.push(self.emit_expr_inline(heap.car(a), heap, syms));
                            a = heap.cdr(a);
                        }
                        let mut out = String::new();
                        for (i, arg) in args.iter().enumerate() {
                            out.push_str(&format!("{pad}let __t{i} = {arg};\n"));
                        }
                        for (i, p) in params.iter().enumerate() {
                            out.push_str(&format!("{pad}{} = __t{i};\n", rust_ident(p)));
                        }
                        out.push_str(&format!("{pad}continue;\n"));
                        return out;
                    }

                    // Not a self-tail-call — use emit_expr_inline + tco_return
                    let code = self.emit_expr_inline(expr, heap, syms);
                    return self.tco_return(&pad, &code);
                }
            }
        }

        // Non-symbol head — use emit_expr_inline + tco_return
        let code = self.emit_expr_inline(expr, heap, syms);
        self.tco_return(&pad, &code)
    }

    /// Emit an expression as an inline Rust expression (no trailing newline).
    fn emit_expr_inline(&self, expr: Val, heap: &Heap, syms: &SymbolTable) -> String {
        if expr.is_fixnum() {
            return format!("Val::fixnum({})", expr.as_fixnum().unwrap());
        }
        if expr == Val::NIL {
            return "Val::NIL".to_string();
        }
        if !expr.is_rib() {
            return "Val::NIL".to_string();
        }
        let tag = heap.tag(expr);
        if tag == table::T_SYM {
            let name = syms.symbol_name(expr).unwrap_or("_");
            // Known function in value position → wrap as closure
            if let Some(id) = self.function_closure_id(name) {
                return format!("make_closure({id}, Val::NIL)");
            }
            // Callable builtin in value position → wrap as closure
            if Self::is_callable_builtin(name) {
                let id = self.get_or_create_builtin_closure(name);
                return format!("make_closure({id} as i64, Val::NIL)");
            }
            if self.is_global(name) {
                return format!("unsafe {{ {} }}", rust_ident(name));
            }
            return rust_ident(name);
        }
        if tag == table::T_STR {
            return self.emit_string_rib(expr, heap);
        }
        if tag == table::T_CHAR {
            let cp = heap.rib_car(expr).as_fixnum().unwrap_or(0);
            return format!("make_char({cp})");
        }
        if tag == table::TRUE {
            return "TRUE_VAL".to_string();
        }
        if tag == table::BOT {
            return "FALSE_VAL".to_string();
        }
        if tag != table::T_PAIR {
            return "Val::NIL".to_string();
        }

        let head = heap.car(expr);
        let rest = heap.cdr(expr);

        if heap.is_symbol(head) {
            let name = syms.symbol_name(head).unwrap_or("");
            match name {
                "+" | "*" => {
                    let mut args = Vec::new();
                    let mut r = rest;
                    while heap.is_pair(r) {
                        args.push(self.emit_expr_inline(heap.car(r), heap, syms));
                        r = heap.cdr(r);
                    }
                    let op = if name == "+" { "+" } else { "*" };
                    let chain = args.iter()
                        .map(|a| format!("{a}.as_fixnum().unwrap()"))
                        .collect::<Vec<_>>()
                        .join(&format!(" {op} "));
                    return format!("Val::fixnum({chain})");
                }
                "-" | "/" | "quotient" | "remainder" | "modulo" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    if name == "-" && heap.cdr(rest) == Val::NIL {
                        return format!("Val::fixnum(-{a}.as_fixnum().unwrap())");
                    }
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    let op = match name { "-" => "-", "/" | "quotient" => "/",
                                          "remainder" | "modulo" => "%", _ => "-" };
                    return format!("Val::fixnum({a}.as_fixnum().unwrap() {op} {b}.as_fixnum().unwrap())");
                }
                "=" | "<" | ">" | "<=" | ">=" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    let op = match name { "=" => "==", "<" => "<", ">" => ">",
                                          "<=" => "<=", ">=" => ">=", _ => "==" };
                    return format!("bool_to_val({a}.as_fixnum().unwrap() {op} {b}.as_fixnum().unwrap())");
                }
                "cons" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("cons({a}, {b})");
                }
                "car" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("car({a})");
                }
                "cdr" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("cdr({a})");
                }
                "if" => {
                    let test = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let r2 = heap.cdr(rest);
                    let c = self.emit_expr_inline(heap.car(r2), heap, syms);
                    let alt_list = heap.cdr(r2);
                    let a = if heap.is_pair(alt_list) {
                        self.emit_expr_inline(heap.car(alt_list), heap, syms)
                    } else {
                        "Val::NIL".to_string()
                    };
                    return format!("if is_true({test}) {{ {c} }} else {{ {a} }}");
                }
                "null?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val({a} == Val::NIL)");
                }
                "pair?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val({a} != Val::NIL && !{a}.is_fixnum())");
                }
                "number?" | "integer?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val({a}.is_fixnum())");
                }
                "zero?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val({a}.as_fixnum() == Some(0))");
                }
                "positive?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val({a}.as_fixnum().map_or(false, |n| n > 0))");
                }
                "negative?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val({a}.as_fixnum().map_or(false, |n| n < 0))");
                }
                "even?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val({a}.as_fixnum().unwrap() % 2 == 0)");
                }
                "odd?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val({a}.as_fixnum().unwrap() % 2 != 0)");
                }
                "not" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val(!is_true({a}))");
                }
                "eq?" | "eqv?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val({a} == {b})");
                }
                "abs" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("Val::fixnum({a}.as_fixnum().unwrap().abs())");
                }
                "max" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("Val::fixnum({a}.as_fixnum().unwrap().max({b}.as_fixnum().unwrap()))");
                }
                "min" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("Val::fixnum({a}.as_fixnum().unwrap().min({b}.as_fixnum().unwrap()))");
                }
                "length" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("{{ let mut n = 0i64; let mut l = {a}; while l != Val::NIL && !l.is_fixnum() {{ n += 1; l = cdr(l); }} Val::fixnum(n) }}");
                }
                "list" => {
                    let mut args = Vec::new();
                    let mut r = rest;
                    while heap.is_pair(r) {
                        args.push(self.emit_expr_inline(heap.car(r), heap, syms));
                        r = heap.cdr(r);
                    }
                    let mut s = "Val::NIL".to_string();
                    for arg in args.iter().rev() {
                        s = format!("cons({arg}, {s})");
                    }
                    return s;
                }
                "reverse" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("{{ let mut r = Val::NIL; let mut l = {a}; while l != Val::NIL && !l.is_fixnum() {{ r = cons(car(l), r); l = cdr(l); }} r }}");
                }
                "append" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("append({a}, {b})");
                }
                "display" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("{{ display({a}); Val::NIL }}");
                }
                "newline" => {
                    return "{ println!(); Val::NIL }".to_string();
                }
                "and" => {
                    let mut parts = Vec::new();
                    let mut r = rest;
                    while heap.is_pair(r) {
                        parts.push(self.emit_expr_inline(heap.car(r), heap, syms));
                        r = heap.cdr(r);
                    }
                    if parts.is_empty() { return "Val::fixnum(1)".to_string(); }
                    return self.emit_and_chain(&parts);
                }
                "or" => {
                    let mut parts = Vec::new();
                    let mut r = rest;
                    while heap.is_pair(r) {
                        parts.push(self.emit_expr_inline(heap.car(r), heap, syms));
                        r = heap.cdr(r);
                    }
                    if parts.is_empty() { return "Val::NIL".to_string(); }
                    return self.emit_or_chain(&parts);
                }
                "gcd" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("{{ let (mut a, mut b) = ({a}.as_fixnum().unwrap().abs(), {b}.as_fixnum().unwrap().abs()); while b != 0 {{ let t = b; b = a % b; a = t; }} Val::fixnum(a) }}");
                }
                "set!" => {
                    let var = heap.car(rest);
                    let val_expr = heap.car(heap.cdr(rest));
                    let vname = syms.symbol_name(var).unwrap_or("_");
                    let val_code = self.emit_expr_inline(val_expr, heap, syms);
                    if self.is_global(vname) {
                        return format!("{{ unsafe {{ {} = {val_code}; }} Val::NIL }}", rust_ident(vname));
                    }
                    return format!("{{ {} = {val_code}; Val::NIL }}", rust_ident(vname));
                }
                "set-car!" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("{{ set_car({a}, {b}); Val::NIL }}");
                }
                "set-cdr!" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("{{ set_cdr({a}, {b}); Val::NIL }}");
                }
                "quote" => {
                    let datum = heap.car(rest);
                    return self.emit_datum(datum, heap, syms);
                }
                // ── String / char builtins ────────────
                "string-length" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("string_length({a})");
                }
                "string-ref" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("string_ref({a}, {b})");
                }
                "string-append" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("string_append({a}, {b})");
                }
                "string=?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val(string_eq({a}, {b}))");
                }
                "string<?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val(string_cmp({a}, {b}) < 0)");
                }
                "string>?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val(string_cmp({a}, {b}) > 0)");
                }
                "string<=?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val(string_cmp({a}, {b}) <= 0)");
                }
                "string>=?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val(string_cmp({a}, {b}) >= 0)");
                }
                "string?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val(is_string({a}))");
                }
                "substring" => {
                    let s = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let start = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    let end = self.emit_expr_inline(heap.car(heap.cdr(heap.cdr(rest))), heap, syms);
                    return format!("substring({s}, {start}, {end})");
                }
                "make-string" => {
                    let n = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let fill_rest = heap.cdr(rest);
                    let fill = if heap.is_pair(fill_rest) {
                        self.emit_expr_inline(heap.car(fill_rest), heap, syms)
                    } else {
                        "Val::fixnum(32)".to_string()
                    };
                    return format!("make_string_fill({n}, {fill})");
                }
                "char->integer" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("char_to_integer({a})");
                }
                "integer->char" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("make_char({a}.as_fixnum().unwrap())");
                }
                "char?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val(is_char({a}))");
                }
                "number->string" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("number_to_string({a})");
                }
                "string->number" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("string_to_number({a})");
                }
                "string-set!" => {
                    let s = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let idx = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    let ch = self.emit_expr_inline(heap.car(heap.cdr(heap.cdr(rest))), heap, syms);
                    return format!("string_set({s}, {idx}, {ch})");
                }
                // Case-sensitive char comparisons
                "char=?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val(char_codepoint({a}) == char_codepoint({b}))");
                }
                "char<?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val(char_codepoint({a}) < char_codepoint({b}))");
                }
                "char>?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val(char_codepoint({a}) > char_codepoint({b}))");
                }
                "char<=?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val(char_codepoint({a}) <= char_codepoint({b}))");
                }
                "char>=?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val(char_codepoint({a}) >= char_codepoint({b}))");
                }
                // Case-insensitive char comparisons
                "char-ci=?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val(char_ci_cmp({a}, {b}) == 0)");
                }
                "char-ci<?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val(char_ci_cmp({a}, {b}) < 0)");
                }
                "char-ci>?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val(char_ci_cmp({a}, {b}) > 0)");
                }
                "char-ci<=?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val(char_ci_cmp({a}, {b}) <= 0)");
                }
                "char-ci>=?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val(char_ci_cmp({a}, {b}) >= 0)");
                }
                // Case-insensitive string comparisons
                "string-ci=?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val(string_ci_eq({a}, {b}))");
                }
                "string-ci<?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val(string_ci_cmp({a}, {b}) < 0)");
                }
                "string-ci>?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val(string_ci_cmp({a}, {b}) > 0)");
                }
                "string-ci<=?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val(string_ci_cmp({a}, {b}) <= 0)");
                }
                "string-ci>=?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val(string_ci_cmp({a}, {b}) >= 0)");
                }
                // Char predicates and case conversion
                "char-alphabetic?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val((char_codepoint({a}) as u8).is_ascii_alphabetic())");
                }
                "char-numeric?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val((char_codepoint({a}) as u8).is_ascii_digit())");
                }
                "char-whitespace?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val((char_codepoint({a}) as u8).is_ascii_whitespace())");
                }
                "char-upper-case?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val((char_codepoint({a}) as u8).is_ascii_uppercase())");
                }
                "char-lower-case?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val((char_codepoint({a}) as u8).is_ascii_lowercase())");
                }
                "char-upcase" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("make_char((char_codepoint({a}) as u8).to_ascii_uppercase() as i64)");
                }
                "char-downcase" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("make_char((char_codepoint({a}) as u8).to_ascii_lowercase() as i64)");
                }

                // ── Missing builtins ────────────
                "equal?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val(scheme_equal({a}, {b}))");
                }
                "boolean?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val({a} == TRUE_VAL || {a} == FALSE_VAL)");
                }
                "procedure?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val(!{a}.is_fixnum() && {a} != Val::NIL && unsafe {{ HEAP[{a}.as_rib()].tag == TAG_CLS }})");
                }
                "exact?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val({a}.is_fixnum())");
                }
                "inexact?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val(!{a}.is_fixnum())");
                }
                "expt" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("Val::fixnum({a}.as_fixnum().unwrap().pow({b}.as_fixnum().unwrap() as u32))");
                }
                "lcm" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("{{ let (a, b) = ({a}.as_fixnum().unwrap().abs(), {b}.as_fixnum().unwrap().abs()); if a == 0 || b == 0 {{ Val::fixnum(0) }} else {{ let (mut x, mut y) = (a, b); while y != 0 {{ let t = y; y = x % y; x = t; }} Val::fixnum(a / x * b) }} }}");
                }
                "list-ref" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("list_ref({a}, {b}.as_fixnum().unwrap())");
                }
                "list-tail" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("list_tail({a}, {b}.as_fixnum().unwrap())");
                }
                "apply" => {
                    let f = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let mut args = Vec::new();
                    let mut a = heap.cdr(rest);
                    while heap.is_pair(a) {
                        args.push(self.emit_expr_inline(heap.car(a), heap, syms));
                        a = heap.cdr(a);
                    }
                    if args.len() == 1 {
                        return format!("apply_val({f}, {})", args[0]);
                    }
                    return format!("scheme_apply({f}, &[{}])", args.join(", "));
                }
                "map" => {
                    let f = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let lst = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("scheme_map({f}, {lst})");
                }
                "for-each" => {
                    let f = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let lst = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("{{ scheme_for_each({f}, {lst}); Val::NIL }}");
                }
                "write" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("{{ scheme_write({a}); Val::NIL }}");
                }
                "write-char" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    if heap.is_pair(heap.cdr(rest)) {
                        let p = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                        return format!("write_char_port({a}, {p})");
                    }
                    return format!("{{ let __cp = if is_char({a}) {{ car({a}).as_fixnum().unwrap_or(0) }} else {{ {a}.as_fixnum().unwrap_or(0) }}; print!(\"{{}}\" , __cp as u8 as char); Val::NIL }}");
                }
                // ── Vector operations ────────────
                "make-vector" => {
                    let n = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let fill = if heap.is_pair(heap.cdr(rest)) {
                        self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms)
                    } else { "Val::fixnum(0)".to_string() };
                    return format!("make_vector_fill({n}.as_fixnum().unwrap(), {fill})");
                }
                "vector-length" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("vector_length({a})");
                }
                "vector-ref" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("vector_ref({a}, {b}.as_fixnum().unwrap())");
                }
                "vector-set!" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    let c = self.emit_expr_inline(heap.car(heap.cdr(heap.cdr(rest))), heap, syms);
                    return format!("{{ vector_set({a}, {b}.as_fixnum().unwrap(), {c}); Val::NIL }}");
                }
                "vector?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val(is_vector({a}))");
                }
                // ── Algebra extension ────────────
                "dot" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("Val::fixnum(CAYLEY[{a}.as_fixnum().unwrap() as usize][{b}.as_fixnum().unwrap() as usize] as i64)");
                }
                "tau" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("tau({a})");
                }
                "type-valid?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("bool_to_val(CAYLEY[{a}.as_fixnum().unwrap() as usize][{b}.as_fixnum().unwrap() as usize] != TAG_BOT)");
                }
                // ── R7RS: values / call-with-values ────
                "values" => {
                    let mut args = Vec::new();
                    let mut r = rest;
                    while heap.is_pair(r) {
                        args.push(self.emit_expr_inline(heap.car(r), heap, syms));
                        r = heap.cdr(r);
                    }
                    if args.len() == 1 {
                        return args[0].clone(); // single value = just the value
                    }
                    let count = args.len();
                    let mut list = "Val::NIL".to_string();
                    for a in args.iter().rev() {
                        list = format!("cons({a}, {list})");
                    }
                    return format!("make_values({list}, {count})");
                }
                "call-with-values" => {
                    let producer = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let consumer = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("call_with_values({producer}, {consumer})");
                }
                // ── R7RS: error / raise ──────────────
                "error" => {
                    let msg = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let mut irritants = Vec::new();
                    let mut r = heap.cdr(rest);
                    while heap.is_pair(r) {
                        irritants.push(self.emit_expr_inline(heap.car(r), heap, syms));
                        r = heap.cdr(r);
                    }
                    let mut irr_list = "Val::NIL".to_string();
                    for i in irritants.iter().rev() {
                        irr_list = format!("cons({i}, {irr_list})");
                    }
                    return format!("scheme_raise(make_error({msg}, {irr_list}))");
                }
                "raise" => {
                    let obj = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("scheme_raise({obj})");
                }
                "error-object?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val(is_error_object({a}))");
                }
                "error-object-message" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("car({a})");
                }
                "error-object-irritants" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("cdr({a})");
                }
                "call-with-current-continuation" | "call/cc" => {
                    let proc = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("call_with_current_continuation({proc})");
                }
                "with-exception-handler" => {
                    let handler = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let thunk = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("with_exception_handler({handler}, {thunk})");
                }
                "guard" => {
                    // (guard (var (test expr) ...) body ...)
                    let var_clauses = heap.car(rest);
                    let body = heap.cdr(rest);
                    let var = heap.car(var_clauses);
                    let clauses = heap.cdr(var_clauses);
                    let vname = syms.symbol_name(var).unwrap_or("_");
                    let rv = rust_ident(vname);

                    // Emit: match scheme_guard(|| { body }) { Ok(v) => v, Err(e) => { cond... } }
                    let mut body_parts = Vec::new();
                    let mut b = body;
                    while heap.is_pair(b) {
                        body_parts.push(self.emit_expr_inline(heap.car(b), heap, syms));
                        b = heap.cdr(b);
                    }
                    let body_code = if body_parts.len() == 1 {
                        body_parts[0].clone()
                    } else {
                        let last = body_parts.pop().unwrap();
                        let stmts = body_parts.iter().map(|p| format!("{p};")).collect::<Vec<_>>().join(" ");
                        format!("{{ {stmts} {last} }}")
                    };

                    let mut out = format!("match scheme_guard(|| {{ {body_code} }}) {{ Ok(__v) => __v, Err({rv}) => {{ ");
                    // Emit cond clauses
                    let mut first = true;
                    let mut c = clauses;
                    while heap.is_pair(c) {
                        let clause = heap.car(c);
                        let test = heap.car(clause);
                        let clause_body = heap.cdr(clause);
                        if heap.is_symbol(test) && syms.sym_eq(test, "else") {
                            if !first { out.push_str(" else { "); }
                            let mut parts = Vec::new();
                            let mut r = clause_body;
                            while heap.is_pair(r) {
                                parts.push(self.emit_expr_inline(heap.car(r), heap, syms));
                                r = heap.cdr(r);
                            }
                            if let Some(last) = parts.pop() {
                                for p in &parts { out.push_str(&format!("{p}; ")); }
                                out.push_str(&last);
                            }
                            if !first { out.push_str(" }"); }
                        } else {
                            let test_code = self.emit_expr_inline(test, heap, syms);
                            if first {
                                out.push_str(&format!("if is_true({test_code}) {{ "));
                            } else {
                                out.push_str(&format!(" else if is_true({test_code}) {{ "));
                            }
                            let mut parts = Vec::new();
                            let mut r = clause_body;
                            while heap.is_pair(r) {
                                parts.push(self.emit_expr_inline(heap.car(r), heap, syms));
                                r = heap.cdr(r);
                            }
                            if let Some(last) = parts.pop() {
                                for p in &parts { out.push_str(&format!("{p}; ")); }
                                out.push_str(&last);
                            }
                            out.push_str(" }");
                        }
                        first = false;
                        c = heap.cdr(c);
                    }
                    if !first {
                        // Add else branch that re-raises if no clause matched
                        out.push_str(&format!(" else {{ scheme_raise({rv}) }}"));
                    }
                    out.push_str(" } }");
                    return out;
                }
                // ── Ports / I/O ──────────────────
                "read" => {
                    return "scheme_read()".to_string();
                }
                "current-input-port" => {
                    return "current_input_port()".to_string();
                }
                "current-output-port" => {
                    return "current_output_port()".to_string();
                }
                "current-error-port" => {
                    return "current_error_port()".to_string();
                }
                "open-input-file" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("open_input_file({a})");
                }
                "open-output-file" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("open_output_file({a})");
                }
                "close-port" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("close_port({a})");
                }
                "read-char" => {
                    if heap.is_pair(rest) {
                        let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                        return format!("read_char_port({a})");
                    }
                    return "read_char_port(current_input_port())".to_string();
                }
                "peek-char" => {
                    if heap.is_pair(rest) {
                        let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                        return format!("peek_char_port({a})");
                    }
                    return "peek_char_port(current_input_port())".to_string();
                }
                "read-line" => {
                    if heap.is_pair(rest) {
                        let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                        return format!("read_line_port({a})");
                    }
                    return "read_line_port(current_input_port())".to_string();
                }
                "write-string" => {
                    let s = self.emit_expr_inline(heap.car(rest), heap, syms);
                    if heap.is_pair(heap.cdr(rest)) {
                        let p = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                        return format!("write_string_port({s}, {p})");
                    }
                    return format!("write_string_port({s}, current_output_port())");
                }
                "port?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val(is_port({a}))");
                }
                "input-port?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val(is_port({a}) && port_direction({a}) == 0)");
                }
                "output-port?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val(is_port({a}) && port_direction({a}) == 1)");
                }
                "eof-object" => {
                    return "EOF_VAL".to_string();
                }
                "eof-object?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("bool_to_val({a} == EOF_VAL)");
                }
                "strict-mode" => {
                    return "Val::NIL".to_string();
                }
                "permissive-mode" => {
                    return "Val::NIL".to_string();
                }
                "begin" => {
                    let mut parts = Vec::new();
                    let mut r = rest;
                    while heap.is_pair(r) {
                        parts.push(self.emit_expr_inline(heap.car(r), heap, syms));
                        r = heap.cdr(r);
                    }
                    if parts.is_empty() { return "Val::NIL".to_string(); }
                    if parts.len() == 1 { return parts[0].clone(); }
                    let last = parts.pop().unwrap();
                    let stmts = parts.iter().map(|p| format!("{p};")).collect::<Vec<_>>().join(" ");
                    return format!("{{ {stmts} {last} }}");
                }
                "let" | "let*" => {
                    let first = heap.car(rest);
                    if name == "let" && heap.is_symbol(first) {
                        // Named let — wrap emit_expr output as block
                        let code = self.emit_expr(expr, heap, syms, 0);
                        return format!("{{ {} }}", code.trim());
                    }
                    let bindings = first;
                    let body = heap.cdr(rest);
                    let mut out = "{ ".to_string();
                    let mut b = bindings;
                    while heap.is_pair(b) {
                        let binding = heap.car(b);
                        let var = heap.car(binding);
                        let init = heap.car(heap.cdr(binding));
                        let vname = syms.symbol_name(var).unwrap_or("_");
                        let init_code = self.emit_expr_inline(init, heap, syms);
                        let mutk = if self.is_set_target(vname) { "mut " } else { "" };
                        out.push_str(&format!("let {mutk}{} = {init_code}; ", rust_ident(vname)));
                        b = heap.cdr(b);
                    }
                    let mut parts = Vec::new();
                    let mut r = body;
                    while heap.is_pair(r) {
                        parts.push(self.emit_expr_inline(heap.car(r), heap, syms));
                        r = heap.cdr(r);
                    }
                    if let Some(last) = parts.pop() {
                        for p in &parts { out.push_str(&format!("{p}; ")); }
                        out.push_str(&last);
                    }
                    out.push_str(" }");
                    return out;
                }
                "letrec" => {
                    let bindings = heap.car(rest);
                    let body = heap.cdr(rest);
                    let mut out = "{ ".to_string();
                    let mut b = bindings;
                    while heap.is_pair(b) {
                        let binding = heap.car(b);
                        let var = heap.car(binding);
                        let vname = syms.symbol_name(var).unwrap_or("_");
                        out.push_str(&format!("let mut {} = Val::NIL; ", rust_ident(vname)));
                        b = heap.cdr(b);
                    }
                    b = bindings;
                    while heap.is_pair(b) {
                        let binding = heap.car(b);
                        let var = heap.car(binding);
                        let init = heap.car(heap.cdr(binding));
                        let vname = syms.symbol_name(var).unwrap_or("_");
                        let init_code = self.emit_expr_inline(init, heap, syms);
                        out.push_str(&format!("{} = {init_code}; ", rust_ident(vname)));
                        b = heap.cdr(b);
                    }
                    // Patch closure envs so mutual references see final values
                    b = bindings;
                    while heap.is_pair(b) {
                        let binding = heap.car(b);
                        let var = heap.car(binding);
                        let init = heap.car(heap.cdr(binding));
                        let vname = syms.symbol_name(var).unwrap_or("_");
                        if heap.is_pair(init) {
                            let init_head = heap.car(init);
                            if heap.is_symbol(init_head) {
                                let iname = syms.symbol_name(init_head).unwrap_or("");
                                if iname == "lambda" || iname == "case-lambda" {
                                    let params_list = heap.car(heap.cdr(init));
                                    let body_list = heap.cdr(heap.cdr(init));
                                    let mut param_bound: HashSet<String> = HashSet::new();
                                    if heap.is_symbol(params_list) {
                                        if let Some(pn) = syms.symbol_name(params_list) {
                                            param_bound.insert(pn.to_string());
                                        }
                                    } else {
                                        let mut p = params_list;
                                        while heap.is_pair(p) {
                                            if let Some(pn) = syms.symbol_name(heap.car(p)) {
                                                param_bound.insert(pn.to_string());
                                            }
                                            p = heap.cdr(p);
                                        }
                                        if heap.is_symbol(p) {
                                            if let Some(pn) = syms.symbol_name(p) {
                                                param_bound.insert(pn.to_string());
                                            }
                                        }
                                    }
                                    let fvs = self.collect_free_vars_list(body_list, heap, syms, &param_bound);
                                    if !fvs.is_empty() {
                                        let rv = rust_ident(vname);
                                        let mut env = "Val::NIL".to_string();
                                        for fv in fvs.iter().rev() {
                                            env = format!("cons({}, {env})", rust_ident(fv));
                                        }
                                        out.push_str(&format!("set_cdr({rv}, {env}); "));
                                    }
                                }
                            }
                        }
                        b = heap.cdr(b);
                    }
                    let mut parts = Vec::new();
                    let mut r = body;
                    while heap.is_pair(r) {
                        parts.push(self.emit_expr_inline(heap.car(r), heap, syms));
                        r = heap.cdr(r);
                    }
                    if let Some(last) = parts.pop() {
                        for p in &parts { out.push_str(&format!("{p}; ")); }
                        out.push_str(&last);
                    }
                    out.push_str(" }");
                    return out;
                }
                "cond" => {
                    // Inline version of emit_cond — produces a block expression
                    let code = self.emit_cond(rest, heap, syms, 0);
                    return format!("{{ {} }}", code.trim());
                }
                "case" => {
                    // Inline version of emit_case — produces a block expression
                    let code = self.emit_case(rest, heap, syms, 0);
                    return format!("{{ {} }}", code.trim());
                }
                "do" => {
                    // Inline version of emit_do — produces a block expression
                    let var_specs = heap.car(rest);
                    let test_clause = heap.car(heap.cdr(rest));
                    let commands = heap.cdr(heap.cdr(rest));

                    let mut out = "{ ".to_string();

                    // Initialize vars
                    let mut vars = Vec::new();
                    let mut vs = var_specs;
                    while heap.is_pair(vs) {
                        let spec = heap.car(vs);
                        let var = heap.car(spec);
                        let init = heap.car(heap.cdr(spec));
                        let step_rest = heap.cdr(heap.cdr(spec));
                        let step = if heap.is_pair(step_rest) { Some(heap.car(step_rest)) } else { None };

                        let vname = syms.symbol_name(var).unwrap_or("_").to_string();
                        let init_code = self.emit_expr_inline(init, heap, syms);
                        out.push_str(&format!("let mut {} = {init_code}; ", rust_ident(&vname)));
                        vars.push((vname, step));
                        vs = heap.cdr(vs);
                    }

                    let test_expr = heap.car(test_clause);
                    let result_exprs = heap.cdr(test_clause);

                    out.push_str("loop { ");

                    // Test
                    let test_code = self.emit_expr_inline(test_expr, heap, syms);
                    out.push_str(&format!("if is_true({test_code}) {{ break "));
                    // Result expressions
                    let mut rparts = Vec::new();
                    let mut r = result_exprs;
                    while heap.is_pair(r) {
                        rparts.push(self.emit_expr_inline(heap.car(r), heap, syms));
                        r = heap.cdr(r);
                    }
                    if let Some(last) = rparts.pop() {
                        for p in &rparts { out.push_str(&format!("{p}; ")); }
                        out.push_str(&last);
                    } else {
                        out.push_str("Val::NIL");
                    }
                    out.push_str(" } ");

                    // Commands
                    let mut cmd = commands;
                    while heap.is_pair(cmd) {
                        let code = self.emit_expr_inline(heap.car(cmd), heap, syms);
                        out.push_str(&format!("{code}; "));
                        cmd = heap.cdr(cmd);
                    }

                    // Step vars (compute all first, then assign)
                    let mut step_codes = Vec::new();
                    for (vname, step) in &vars {
                        if let Some(step_expr) = step {
                            step_codes.push((vname.clone(), self.emit_expr_inline(*step_expr, heap, syms)));
                        }
                    }
                    for (vname, code) in &step_codes {
                        out.push_str(&format!("let _next_{vn} = {code}; ", vn = rust_ident(vname)));
                    }
                    for (vname, _) in &step_codes {
                        out.push_str(&format!("{vn} = _next_{vn}; ", vn = rust_ident(vname)));
                    }

                    out.push_str("} }");
                    return out;
                }
                "lambda" => {
                    return self.compile_lambda(rest, heap, syms);
                }
                "case-lambda" => {
                    return self.compile_case_lambda(rest, heap, syms);
                }
                _ => {
                    let fname = rust_ident(name);
                    let mut args = Vec::new();
                    let mut a = rest;
                    while heap.is_pair(a) {
                        args.push(self.emit_expr_inline(heap.car(a), heap, syms));
                        a = heap.cdr(a);
                    }
                    // Use direct call only when name is a known function AND is not
                    // shadowed by a local parameter in the current function.
                    let shadowed = self.current_params.borrow().contains(name);
                    if self.is_known_function(name) && !shadowed {
                        if self.is_variadic_function(name) {
                            return format!("{fname}(&[{}])", args.join(", "));
                        }
                        return format!("{fname}({})", args.join(", "));
                    } else if self.is_global(name) {
                        return format!("call_val(unsafe {{ {fname} }}, &[{}])", args.join(", "));
                    } else {
                        return format!("call_val({fname}, &[{}])", args.join(", "));
                    }
                }
            }
        }

        // Generic call (head is not a symbol) — e.g. ((lambda ...) args)
        {
            let head_code = self.emit_expr_inline(head, heap, syms);
            let mut args = Vec::new();
            let mut a = rest;
            while heap.is_pair(a) {
                args.push(self.emit_expr_inline(heap.car(a), heap, syms));
                a = heap.cdr(a);
            }
            let args_str = args.join(", ");
            format!("call_val({head_code}, &[{args_str}])")
        }
    }

    fn emit_begin(&self, mut body: Val, heap: &Heap, syms: &SymbolTable, indent: usize) -> String {
        let mut out = String::new();
        while heap.is_pair(body) {
            let is_last = heap.cdr(body) == Val::NIL;
            if is_last {
                out.push_str(&self.emit_expr(heap.car(body), heap, syms, indent));
            } else {
                let code = self.emit_expr_inline(heap.car(body), heap, syms);
                let pad = "    ".repeat(indent);
                out.push_str(&format!("{pad}{code};\n"));
            }
            body = heap.cdr(body);
        }
        out
    }

    fn emit_cond(&self, mut clauses: Val, heap: &Heap, syms: &SymbolTable, indent: usize) -> String {
        let pad = "    ".repeat(indent);
        let mut out = String::new();
        let mut first = true;

        while heap.is_pair(clauses) {
            let clause = heap.car(clauses);
            let test = heap.car(clause);
            let body = heap.cdr(clause);

            if heap.is_symbol(test) && syms.sym_eq(test, "else") {
                out.push_str(&format!("{pad}}} else {{\n"));
                out.push_str(&self.emit_begin(body, heap, syms, indent + 1));
                out.push_str(&format!("{pad}}}\n"));
                return out;
            }

            let test_code = self.emit_expr_inline(test, heap, syms);
            if first {
                out.push_str(&format!("{pad}if is_true({test_code}) {{\n"));
                first = false;
            } else {
                out.push_str(&format!("{pad}}} else if is_true({test_code}) {{\n"));
            }
            out.push_str(&self.emit_begin(body, heap, syms, indent + 1));
            clauses = heap.cdr(clauses);
        }

        if !first {
            out.push_str(&format!("{pad}}} else {{\n{pad}    Val::NIL\n{pad}}}\n"));
        }
        out
    }

    fn emit_and_chain(&self, parts: &[String]) -> String {
        if parts.is_empty() { return "Val::fixnum(1)".to_string(); }
        if parts.len() == 1 { return parts[0].clone(); }
        let mut s = format!("{{ let _v = {}; if !is_true(_v) {{ _v }}", parts[0]);
        for p in &parts[1..parts.len()-1] {
            s.push_str(&format!(" else {{ let _v = {}; if !is_true(_v) {{ _v }}", p));
        }
        s.push_str(&format!(" else {{ {} }}", parts.last().unwrap()));
        // Close all else-blocks opened above (one per element except the last, plus the outer block)
        for _ in 0..parts.len()-1 { s.push_str(" }"); }
        s
    }

    fn emit_or_chain(&self, parts: &[String]) -> String {
        if parts.is_empty() { return "Val::NIL".to_string(); }
        if parts.len() == 1 { return parts[0].clone(); }
        // Build: { let _v = p0; if is_true(_v) { _v } else { let _v = p1; if is_true(_v) { _v } else { pN } } }
        let mut s = format!("{{ let _v = {}; if is_true(_v) {{ _v }}", parts[0]);
        for p in &parts[1..parts.len()-1] {
            s.push_str(&format!(" else {{ let _v = {}; if is_true(_v) {{ _v }}", p));
        }
        s.push_str(&format!(" else {{ {} }}", parts.last().unwrap()));
        // Close: one for each else block + one for the outer
        for _ in 0..parts.len()-1 { s.push_str(" }"); }
        s
    }

    fn emit_case(&self, rest: Val, heap: &Heap, syms: &SymbolTable, indent: usize) -> String {
        let pad = "    ".repeat(indent);
        let key_expr = heap.car(rest);
        let key_code = self.emit_expr_inline(key_expr, heap, syms);
        let mut out = format!("{pad}{{ let _key = {key_code};\n");

        let mut clauses = heap.cdr(rest);
        let mut first = true;
        while heap.is_pair(clauses) {
            let clause = heap.car(clauses);
            let datums = heap.car(clause);
            let body = heap.cdr(clause);

            if heap.is_symbol(datums) && syms.sym_eq(datums, "else") {
                out.push_str(&format!("{pad}}} else {{\n"));
                out.push_str(&self.emit_begin(body, heap, syms, indent + 1));
                out.push_str(&format!("{pad}}}}}\n"));
                return out;
            }

            // Build condition: _key == datum1 || _key == datum2 || ...
            let mut conds = Vec::new();
            let mut d = datums;
            while heap.is_pair(d) {
                let datum = heap.car(d);
                let dc = self.emit_datum(datum, heap, syms);
                conds.push(format!("_key == {dc}"));
                d = heap.cdr(d);
            }
            let cond = conds.join(" || ");

            if first {
                out.push_str(&format!("{pad}if {cond} {{\n"));
                first = false;
            } else {
                out.push_str(&format!("{pad}}} else if {cond} {{\n"));
            }
            out.push_str(&self.emit_begin(body, heap, syms, indent + 1));
            clauses = heap.cdr(clauses);
        }
        if !first {
            out.push_str(&format!("{pad}}} else {{\n{pad}    Val::NIL\n{pad}}}}}\n"));
        } else {
            out.push_str(&format!("{pad}Val::NIL }}\n"));
        }
        out
    }

    fn emit_do(&self, rest: Val, heap: &Heap, syms: &SymbolTable, indent: usize) -> String {
        let pad = "    ".repeat(indent);
        let var_specs = heap.car(rest);
        let test_clause = heap.car(heap.cdr(rest));
        let commands = heap.cdr(heap.cdr(rest));

        let mut out = format!("{pad}{{\n");

        // Initialize vars
        let mut vars = Vec::new();
        let mut vs = var_specs;
        while heap.is_pair(vs) {
            let spec = heap.car(vs);
            let var = heap.car(spec);
            let init = heap.car(heap.cdr(spec));
            let step_rest = heap.cdr(heap.cdr(spec));
            let step = if heap.is_pair(step_rest) { Some(heap.car(step_rest)) } else { None };

            let vname = syms.symbol_name(var).unwrap_or("_").to_string();
            let init_code = self.emit_expr_inline(init, heap, syms);
            out.push_str(&format!("{pad}    let mut {} = {init_code};\n", rust_ident(&vname)));
            vars.push((vname, step));
            vs = heap.cdr(vs);
        }

        let test_expr = heap.car(test_clause);
        let result_exprs = heap.cdr(test_clause);

        out.push_str(&format!("{pad}    loop {{\n"));

        // Test
        let test_code = self.emit_expr_inline(test_expr, heap, syms);
        out.push_str(&format!("{pad}        if is_true({test_code}) {{ break\n"));
        out.push_str(&self.emit_begin(result_exprs, heap, syms, indent + 3));
        out.push_str(&format!("{pad}        }}\n"));

        // Commands
        let mut cmd = commands;
        while heap.is_pair(cmd) {
            let code = self.emit_expr_inline(heap.car(cmd), heap, syms);
            out.push_str(&format!("{pad}        {code};\n"));
            cmd = heap.cdr(cmd);
        }

        // Step vars (compute all first, then assign)
        let mut step_codes = Vec::new();
        for (vname, step) in &vars {
            if let Some(step_expr) = step {
                step_codes.push((vname.clone(), self.emit_expr_inline(*step_expr, heap, syms)));
            }
        }
        for (vname, code) in &step_codes {
            out.push_str(&format!("{pad}        let _next_{vn} = {code};\n", vn = rust_ident(vname)));
        }
        for (vname, _) in &step_codes {
            out.push_str(&format!("{pad}        {vn} = _next_{vn};\n", vn = rust_ident(vname)));
        }

        out.push_str(&format!("{pad}    }}\n"));
        out.push_str(&format!("{pad}}}\n"));
        out
    }

    fn emit_datum(&self, datum: Val, heap: &Heap, syms: &SymbolTable) -> String {
        if datum.is_fixnum() {
            return format!("Val::fixnum({})", datum.as_fixnum().unwrap());
        }
        if datum == Val::NIL {
            return "Val::NIL".to_string();
        }
        if heap.is_symbol(datum) {
            // Quoted symbol — for now, emit as a fixnum hash
            let name = syms.symbol_name(datum).unwrap_or("_");
            let hash = name.bytes().fold(0i64, |acc, b| acc.wrapping_mul(31).wrapping_add(b as i64));
            return format!("Val::fixnum({hash}) /* '{name} */");
        }
        if heap.tag(datum) == table::T_STR {
            return self.emit_string_rib(datum, heap);
        }
        if heap.tag(datum) == table::T_CHAR {
            let cp = heap.rib_car(datum).as_fixnum().unwrap_or(0);
            return format!("make_char({cp})");
        }
        if heap.is_pair(datum) {
            // Quoted list — recursively emit
            let car_code = self.emit_datum(heap.car(datum), heap, syms);
            let cdr_code = self.emit_datum(heap.cdr(datum), heap, syms);
            return format!("cons({car_code}, {cdr_code})");
        }
        "Val::NIL".to_string()
    }

    /// Emit code that constructs a string rib at runtime from a parsed string Val.
    fn emit_string_rib(&self, str_val: Val, heap: &Heap) -> String {
        // Walk the char list in the string rib
        let mut bytes = Vec::new();
        let mut chars = heap.rib_car(str_val);
        while heap.is_pair(chars) {
            if let Some(cp) = heap.car(chars).as_fixnum() {
                bytes.push(cp);
            }
            chars = heap.cdr(chars);
        }
        let len = bytes.len();
        // Build: { let c = cons(fixnum(h), cons(fixnum(e), ...NIL)); make_string(c, fixnum(len)) }
        let mut s = "Val::NIL".to_string();
        for &b in bytes.iter().rev() {
            s = format!("cons(Val::fixnum({b}), {s})");
        }
        format!("{{ let __c = {s}; make_string(__c, Val::fixnum({len} as i64)) }}")
    }
}

/// Convert a Scheme identifier to a valid Rust identifier.
fn rust_ident(name: &str) -> String {
    let mut s = String::new();
    for c in name.chars() {
        match c {
            '-' => s.push('_'),
            '?' => s.push_str("_p"),
            '!' => s.push_str("_bang"),
            '>' => s.push_str("_to_"),
            '<' => s.push_str("_lt_"),
            '=' => s.push_str("_eq_"),
            '*' => s.push_str("_star_"),
            '+' => s.push_str("_plus_"),
            '/' => s.push_str("_div_"),
            _ => s.push(c),
        }
    }
    // Avoid Rust keywords
    match s.as_str() {
        "type" => "type_".to_string(),
        "match" => "match_".to_string(),
        "loop" => "loop_".to_string(),
        "fn" => "fn_".to_string(),
        "let" => "let_".to_string(),
        "if" => "if_".to_string(),
        "else" => "else_".to_string(),
        "return" => "return_".to_string(),
        "mod" => "mod_".to_string(),
        "do" => "do_".to_string(),
        "while" => "while_".to_string(),
        "for" => "for_".to_string(),
        "in" => "in_".to_string(),
        "ref" => "ref_".to_string(),
        "mut" => "mut_".to_string(),
        "move" => "move_".to_string(),
        "self" => "self_".to_string(),
        "super" => "super_".to_string(),
        "crate" => "crate_".to_string(),
        "struct" => "struct_".to_string(),
        "enum" => "enum_".to_string(),
        "trait" => "trait_".to_string(),
        "impl" => "impl_".to_string(),
        "use" => "use_".to_string(),
        "where" => "where_".to_string(),
        "async" => "async_".to_string(),
        "await" => "await_".to_string(),
        "break" => "break_".to_string(),
        "continue" => "continue_".to_string(),
        "true" => "true_".to_string(),
        "false" => "false_".to_string(),
        _ => s,
    }
}

/// The minimal runtime that gets inlined into compiled output.
/// Uses a global heap to avoid mutable borrow issues in nested expressions.
const RUNTIME_PRELUDE: &str = r#"
// ── Inline runtime ───────────────────────────────────────────────

#[derive(Clone, Copy, PartialEq, Eq)]
struct Val(i64);

impl Val {
    const NIL: Val = Val(0);

    #[inline(always)]
    const fn fixnum(n: i64) -> Val { Val((n << 1) | 1) }

    #[inline(always)]
    const fn rib(idx: usize) -> Val { Val((idx as i64) << 1) }

    #[inline(always)]
    fn is_fixnum(self) -> bool { (self.0 & 1) != 0 }

    #[inline(always)]
    fn as_fixnum(self) -> Option<i64> {
        if self.is_fixnum() { Some(self.0 >> 1) } else { None }
    }

    #[inline(always)]
    fn as_rib(self) -> usize { (self.0 >> 1) as usize }
}

#[derive(Clone, Copy)]
struct Rib { car: Val, cdr: Val, tag: u8 }

static mut HEAP: Vec<Rib> = Vec::new();

// Rib 0 = nil/'(), rib 1 = #f (BOT), rib 2 = #t
const FALSE_VAL: Val = Val(1 << 1); // rib index 1
const TRUE_VAL: Val = Val(2 << 1);  // rib index 2

const EOF_VAL: Val = Val(3 << 1);  // rib index 3

fn heap_init() {
    unsafe { HEAP = Vec::with_capacity(65536);
             HEAP.push(Rib { car: Val::NIL, cdr: Val::NIL, tag: TAG_TOP });  // rib 0: nil
             HEAP.push(Rib { car: Val::NIL, cdr: Val::NIL, tag: TAG_BOT });  // rib 1: #f
             HEAP.push(Rib { car: Val::NIL, cdr: Val::NIL, tag: 20 });       // rib 2: #t
             HEAP.push(Rib { car: Val::NIL, cdr: Val::NIL, tag: TAG_EOF });  // rib 3: eof
             PORTS = Vec::with_capacity(16);
             PORTS.push(PortInner::Stdin(std::io::BufReader::new(std::io::stdin())));
             PORTS.push(PortInner::Stdout);
             PORTS.push(PortInner::Stderr);
    }
}

#[inline]
fn cons(car: Val, cdr: Val) -> Val {
    unsafe {
        let idx = HEAP.len();
        HEAP.push(Rib { car, cdr, tag: TAG_PAIR });
        Val::rib(idx)
    }
}

#[inline(always)]
fn car(v: Val) -> Val {
    if v.is_fixnum() || v == Val::NIL { return Val::NIL; }
    unsafe { HEAP[v.as_rib()].car }
}

#[inline(always)]
fn cdr(v: Val) -> Val {
    if v.is_fixnum() || v == Val::NIL { return Val::NIL; }
    unsafe { HEAP[v.as_rib()].cdr }
}

#[inline(always)]
fn is_true(v: Val) -> bool {
    // R4RS: only #f is false. '() is truthy.
    v != FALSE_VAL
}

#[inline(always)]
fn bool_to_val(b: bool) -> Val {
    if b { TRUE_VAL } else { FALSE_VAL }
}

fn set_car(v: Val, new_car: Val) {
    if !v.is_fixnum() && v != Val::NIL {
        unsafe { HEAP[v.as_rib()].car = new_car; }
    }
}

fn set_cdr(v: Val, new_cdr: Val) {
    if !v.is_fixnum() && v != Val::NIL {
        unsafe { HEAP[v.as_rib()].cdr = new_cdr; }
    }
}

fn append(a: Val, b: Val) -> Val {
    if a == Val::NIL || a.is_fixnum() { return b; }
    let c = car(a);
    let rest = append(cdr(a), b);
    cons(c, rest)
}

#[inline(always)]
fn tau(v: Val) -> Val {
    if v == Val::NIL { return Val::fixnum(TAG_TOP as i64); }
    if v.is_fixnum() { return Val::fixnum(TAG_TOP as i64); }
    unsafe { Val::fixnum(HEAP[v.as_rib()].tag as i64) }
}

// ── String / char support ────────────────────────────────────────

fn make_string(chars: Val, len: Val) -> Val {
    unsafe {
        let idx = HEAP.len();
        HEAP.push(Rib { car: chars, cdr: len, tag: TAG_STR });
        Val::rib(idx)
    }
}

fn make_char(codepoint: i64) -> Val {
    unsafe {
        let idx = HEAP.len();
        HEAP.push(Rib { car: Val::fixnum(codepoint), cdr: Val::NIL, tag: TAG_CHAR });
        Val::rib(idx)
    }
}

fn is_string(v: Val) -> bool {
    !v.is_fixnum() && v != Val::NIL && unsafe { HEAP[v.as_rib()].tag == TAG_STR }
}

fn is_char(v: Val) -> bool {
    !v.is_fixnum() && v != Val::NIL && unsafe { HEAP[v.as_rib()].tag == TAG_CHAR }
}

fn string_length(s: Val) -> Val {
    if is_string(s) { cdr(s) } else { Val::fixnum(0) }
}

fn string_ref(s: Val, idx: Val) -> Val {
    let n = idx.as_fixnum().unwrap_or(0);
    let mut chars = car(s);
    for _ in 0..n {
        chars = cdr(chars);
    }
    make_char(car(chars).as_fixnum().unwrap_or(0))
}

fn string_eq(a: Val, b: Val) -> bool {
    let mut ca = car(a);
    let mut cb = car(b);
    loop {
        if ca == Val::NIL && cb == Val::NIL { return true; }
        if ca == Val::NIL || cb == Val::NIL { return false; }
        if ca.is_fixnum() || cb.is_fixnum() { return ca == cb; }
        if car(ca) != car(cb) { return false; }
        ca = cdr(ca);
        cb = cdr(cb);
    }
}

fn string_cmp(a: Val, b: Val) -> i64 {
    let mut ca = car(a);
    let mut cb = car(b);
    loop {
        if ca == Val::NIL && cb == Val::NIL { return 0; }
        if ca == Val::NIL { return -1; }
        if cb == Val::NIL { return 1; }
        let va = car(ca).as_fixnum().unwrap_or(0);
        let vb = car(cb).as_fixnum().unwrap_or(0);
        if va != vb { return va - vb; }
        ca = cdr(ca);
        cb = cdr(cb);
    }
}

fn string_append(a: Val, b: Val) -> Val {
    let chars_a = car(a);
    let chars_b = car(b);
    let la = cdr(a).as_fixnum().unwrap_or(0);
    let lb = cdr(b).as_fixnum().unwrap_or(0);
    let merged = append(chars_a, chars_b);
    make_string(merged, Val::fixnum(la + lb))
}

fn substring(s: Val, start: Val, end: Val) -> Val {
    let si = start.as_fixnum().unwrap_or(0);
    let ei = end.as_fixnum().unwrap_or(0);
    let mut chars = car(s);
    for _ in 0..si { chars = cdr(chars); }
    let mut result = Val::NIL;
    let mut collected = Vec::new();
    for _ in si..ei {
        collected.push(car(chars));
        chars = cdr(chars);
    }
    for v in collected.iter().rev() {
        result = cons(*v, result);
    }
    make_string(result, Val::fixnum(ei - si))
}

fn make_string_fill(n: Val, fill: Val) -> Val {
    let len = n.as_fixnum().unwrap_or(0);
    let cp = if is_char(fill) { car(fill).as_fixnum().unwrap_or(32) } else { fill.as_fixnum().unwrap_or(32) };
    let mut chars = Val::NIL;
    for _ in 0..len {
        chars = cons(Val::fixnum(cp), chars);
    }
    make_string(chars, Val::fixnum(len))
}

fn char_to_integer(c: Val) -> Val {
    if is_char(c) { car(c) } else { Val::fixnum(0) }
}

fn char_codepoint(c: Val) -> i64 {
    if is_char(c) { car(c).as_fixnum().unwrap_or(0) } else { 0 }
}

fn char_ci_cmp(a: Val, b: Val) -> i64 {
    let ca = (char_codepoint(a) as u8).to_ascii_lowercase() as i64;
    let cb = (char_codepoint(b) as u8).to_ascii_lowercase() as i64;
    ca - cb
}

fn string_ci_eq(a: Val, b: Val) -> bool {
    let mut ca = car(a);
    let mut cb = car(b);
    loop {
        if ca == Val::NIL && cb == Val::NIL { return true; }
        if ca == Val::NIL || cb == Val::NIL { return false; }
        if ca.is_fixnum() || cb.is_fixnum() { return false; }
        let va = (car(ca).as_fixnum().unwrap_or(0) as u8).to_ascii_lowercase();
        let vb = (car(cb).as_fixnum().unwrap_or(0) as u8).to_ascii_lowercase();
        if va != vb { return false; }
        ca = cdr(ca);
        cb = cdr(cb);
    }
}

fn string_ci_cmp(a: Val, b: Val) -> i64 {
    let mut ca = car(a);
    let mut cb = car(b);
    loop {
        if ca == Val::NIL && cb == Val::NIL { return 0; }
        if ca == Val::NIL { return -1; }
        if cb == Val::NIL { return 1; }
        let va = (car(ca).as_fixnum().unwrap_or(0) as u8).to_ascii_lowercase();
        let vb = (car(cb).as_fixnum().unwrap_or(0) as u8).to_ascii_lowercase();
        if va != vb { return (va as i64) - (vb as i64); }
        ca = cdr(ca);
        cb = cdr(cb);
    }
}

fn string_set(s: Val, idx: Val, ch: Val) -> Val {
    let n = idx.as_fixnum().unwrap_or(0);
    let cp = if is_char(ch) { car(ch).as_fixnum().unwrap_or(0) } else { ch.as_fixnum().unwrap_or(0) };
    let mut chars = car(s);
    for _ in 0..n { chars = cdr(chars); }
    set_car(chars, Val::fixnum(cp));
    Val::NIL
}

fn number_to_string(n: Val) -> Val {
    let num = n.as_fixnum().unwrap_or(0);
    let s = format!("{num}");
    let len = s.len() as i64;
    let mut chars = Val::NIL;
    for b in s.bytes().rev() {
        chars = cons(Val::fixnum(b as i64), chars);
    }
    make_string(chars, Val::fixnum(len))
}

fn string_to_number(s: Val) -> Val {
    let mut chars = car(s);
    let mut num: i64 = 0;
    let mut neg = false;
    let mut first = true;
    while chars != Val::NIL && !chars.is_fixnum() {
        let cp = car(chars).as_fixnum().unwrap_or(0);
        if first && cp == 45 { neg = true; } // '-'
        else if cp >= 48 && cp <= 57 { num = num * 10 + (cp - 48); }
        else { return Val::NIL; } // not a number
        first = false;
        chars = cdr(chars);
    }
    if neg { num = -num; }
    Val::fixnum(num)
}

// ── Display ──────────────────────────────────────────────────────

fn display(v: Val) {
    if v == Val::NIL { print!("()"); }
    else if let Some(n) = v.as_fixnum() { print!("{n}"); }
    else {
        unsafe {
            let rib = &HEAP[v.as_rib()];
            if rib.tag == TAG_PAIR {
                print!("(");
                display(rib.car);
                let mut rest = rib.cdr;
                while rest != Val::NIL && !rest.is_fixnum() && HEAP[rest.as_rib()].tag == TAG_PAIR {
                    print!(" ");
                    display(HEAP[rest.as_rib()].car);
                    rest = HEAP[rest.as_rib()].cdr;
                }
                if rest != Val::NIL {
                    print!(" . ");
                    display(rest);
                }
                print!(")");
            } else if rib.tag == TAG_STR {
                // Walk the char list and print each codepoint
                let mut chars = rib.car;
                while chars != Val::NIL && !chars.is_fixnum() {
                    let cp = HEAP[chars.as_rib()].car.as_fixnum().unwrap_or(0);
                    print!("{}", cp as u8 as char);
                    chars = HEAP[chars.as_rib()].cdr;
                }
            } else if rib.tag == TAG_CHAR {
                let cp = rib.car.as_fixnum().unwrap_or(0);
                print!("{}", cp as u8 as char);
            } else if rib.tag == TAG_BOT {
                print!("{}{}", '\x23', 'f');
            } else if rib.tag == 20 {
                print!("{}{}", '\x23', 't');
            } else {
                print!("<rib>");
            }
        }
    }
}

// ── Closure support ──────────────────────────────────────────────

fn make_closure(code_id: i64, env: Val) -> Val {
    unsafe {
        let idx = HEAP.len();
        HEAP.push(Rib { car: Val::fixnum(code_id), cdr: env, tag: TAG_CLS });
        Val::rib(idx)
    }
}

fn call_val(f: Val, args: &[Val]) -> Val {
    if !f.is_fixnum() && f != Val::NIL {
        unsafe {
            let tag = HEAP[f.as_rib()].tag;
            if tag == TAG_CLS {
                return dispatch_closure(f, args);
            }
            if tag == TAG_CONT {
                let cont_id = HEAP[f.as_rib()].car.as_fixnum().unwrap() as u64;
                let value = if args.is_empty() { Val::NIL } else { args[0] };
                std::panic::resume_unwind(Box::new(ContinuationPayload { value, target_id: cont_id }));
            }
        }
    }
    Val::NIL
}

fn apply_val(f: Val, args_list: Val) -> Val {
    // Unpack a Scheme list into a slice and call_val
    let mut args = Vec::new();
    let mut l = args_list;
    while l != Val::NIL && !l.is_fixnum() {
        args.push(car(l));
        l = cdr(l);
    }
    call_val(f, &args)
}

// ── Records ─────────────────────────────────────────────────────

fn make_record(type_id: i64, fields: Val) -> Val {
    unsafe {
        let idx = HEAP.len();
        HEAP.push(Rib { car: Val::fixnum(type_id), cdr: fields, tag: TAG_RECORD });
        Val::rib(idx)
    }
}

fn is_record_type(v: Val, type_id: i64) -> bool {
    !v.is_fixnum() && v != Val::NIL &&
    unsafe { HEAP[v.as_rib()].tag == TAG_RECORD && HEAP[v.as_rib()].car == Val::fixnum(type_id) }
}

fn record_ref(v: Val, idx: usize) -> Val {
    let mut fields = cdr(v); // fields list
    for _ in 0..idx { fields = cdr(fields); }
    car(fields)
}

fn record_set(v: Val, idx: usize, new_val: Val) {
    let mut fields = cdr(v);
    for _ in 0..idx { fields = cdr(fields); }
    set_car(fields, new_val);
}

// ── Multiple values ─────────────────────────────────────────────

fn make_values(list: Val, count: i64) -> Val {
    unsafe {
        let idx = HEAP.len();
        HEAP.push(Rib { car: list, cdr: Val::fixnum(count), tag: TAG_VALUES });
        Val::rib(idx)
    }
}

fn is_values(v: Val) -> bool {
    !v.is_fixnum() && v != Val::NIL && unsafe { HEAP[v.as_rib()].tag == TAG_VALUES }
}

fn call_with_values(producer: Val, consumer: Val) -> Val {
    let v = call_val(producer, &[]);
    if is_values(v) {
        apply_val(consumer, car(v))
    } else {
        call_val(consumer, &[v])
    }
}

// ── Error objects ───────────────────────────────────────────────

fn make_error(msg: Val, irritants: Val) -> Val {
    unsafe {
        let idx = HEAP.len();
        HEAP.push(Rib { car: msg, cdr: irritants, tag: TAG_ERROR });
        Val::rib(idx)
    }
}

fn is_error_object(v: Val) -> bool {
    !v.is_fixnum() && v != Val::NIL && unsafe { HEAP[v.as_rib()].tag == TAG_ERROR }
}

fn scheme_raise(v: Val) -> Val {
    std::panic::resume_unwind(Box::new(v.0));
}

fn scheme_raise_default(v: Val) {
    // Default handler: display and exit
    if is_error_object(v) {
        eprint!("Error: ");
        display_to(car(v), &mut std::io::stderr().lock());
        let mut irritants = cdr(v);
        while irritants != Val::NIL && !irritants.is_fixnum() {
            eprint!(" ");
            display_to(car(irritants), &mut std::io::stderr().lock());
            irritants = cdr(irritants);
        }
        eprintln!();
    } else {
        eprint!("Error: ");
        display_to(v, &mut std::io::stderr().lock());
        eprintln!();
    }
    std::process::exit(1);
}

fn scheme_guard<F: FnOnce() -> Val>(body: F) -> Result<Val, Val> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(body)) {
        Ok(v) => Ok(v),
        Err(payload) => {
            if let Some(&raw) = payload.downcast_ref::<i64>() {
                Err(Val(raw))
            } else {
                // Not a Scheme exception — re-panic
                std::panic::resume_unwind(payload);
            }
        }
    }
}

fn with_exception_handler(handler: Val, thunk: Val) -> Val {
    match scheme_guard(|| call_val(thunk, &[])) {
        Ok(v) => v,
        Err(e) => call_val(handler, &[e]),
    }
}

// ── Escape continuations ────────────────────────────────────────

struct ContinuationPayload {
    value: Val,
    target_id: u64,
}

static mut NEXT_CONT_ID: u64 = 0;

fn make_continuation(cont_id: u64) -> Val {
    unsafe {
        let idx = HEAP.len();
        HEAP.push(Rib { car: Val::fixnum(cont_id as i64), cdr: Val::NIL, tag: TAG_CONT });
        Val::rib(idx)
    }
}

fn call_with_current_continuation(proc: Val) -> Val {
    unsafe {
        let cont_id = NEXT_CONT_ID;
        NEXT_CONT_ID += 1;
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let k = make_continuation(cont_id);
            call_val(proc, &[k])
        })) {
            Ok(v) => v,
            Err(payload) => {
                if let Some(cp) = payload.downcast_ref::<ContinuationPayload>() {
                    if cp.target_id == cont_id {
                        return cp.value;
                    }
                }
                std::panic::resume_unwind(payload);
            }
        }
    }
}

fn display_to(v: Val, w: &mut dyn std::io::Write) {
    if v == Val::NIL { let _ = write!(w, "()"); }
    else if let Some(n) = v.as_fixnum() { let _ = write!(w, "{n}"); }
    else {
        unsafe {
            let rib = &HEAP[v.as_rib()];
            if rib.tag == TAG_STR {
                let mut chars = rib.car;
                while chars != Val::NIL && !chars.is_fixnum() {
                    let cp = HEAP[chars.as_rib()].car.as_fixnum().unwrap_or(0);
                    let _ = write!(w, "{}", cp as u8 as char);
                    chars = HEAP[chars.as_rib()].cdr;
                }
            } else {
                let _ = write!(w, "<object>");
            }
        }
    }
}

// ── Structural equality ─────────────────────────────────────────

fn scheme_equal(a: Val, b: Val) -> bool {
    if a == b { return true; }
    if a.is_fixnum() || b.is_fixnum() { return false; }
    if a == Val::NIL || b == Val::NIL { return false; }
    unsafe {
        let ra = &HEAP[a.as_rib()];
        let rb = &HEAP[b.as_rib()];
        if ra.tag != rb.tag { return false; }
        if ra.tag == TAG_PAIR {
            return scheme_equal(ra.car, rb.car) && scheme_equal(ra.cdr, rb.cdr);
        }
        if ra.tag == TAG_STR { return string_eq(a, b); }
        if ra.tag == TAG_CHAR { return ra.car == rb.car; }
        false
    }
}

// ── Map / for-each ──────────────────────────────────────────────

fn scheme_map(f: Val, lst: Val) -> Val {
    if lst == Val::NIL || lst.is_fixnum() { return Val::NIL; }
    let head = call_val(f, &[car(lst)]);
    let tail = scheme_map(f, cdr(lst));
    cons(head, tail)
}

fn scheme_for_each(f: Val, lst: Val) {
    let mut l = lst;
    while l != Val::NIL && !l.is_fixnum() {
        call_val(f, &[car(l)]);
        l = cdr(l);
    }
}

// ── Apply ───────────────────────────────────────────────────────

fn scheme_apply(f: Val, args: &[Val]) -> Val {
    // (apply f arg1 arg2 ... list) — last arg is a list to spread
    if args.is_empty() { return call_val(f, &[]); }
    let mut flat = Vec::new();
    for i in 0..args.len()-1 {
        flat.push(args[i]);
    }
    // Unpack the last argument (a list)
    let mut l = args[args.len()-1];
    while l != Val::NIL && !l.is_fixnum() {
        flat.push(car(l));
        l = cdr(l);
    }
    call_val(f, &flat)
}

// ── List ref/tail ───────────────────────────────────────────────

fn list_ref(lst: Val, idx: i64) -> Val {
    let mut l = lst;
    for _ in 0..idx { l = cdr(l); }
    car(l)
}

fn list_tail(lst: Val, idx: i64) -> Val {
    let mut l = lst;
    for _ in 0..idx { l = cdr(l); }
    l
}

// ── Write (with quoting) ────────────────────────────────────────

fn scheme_write(v: Val) {
    if v == Val::NIL { print!("()"); }
    else if let Some(n) = v.as_fixnum() { print!("{n}"); }
    else {
        unsafe {
            let rib = &HEAP[v.as_rib()];
            if rib.tag == TAG_PAIR {
                print!("(");
                scheme_write(rib.car);
                let mut rest = rib.cdr;
                while rest != Val::NIL && !rest.is_fixnum() && HEAP[rest.as_rib()].tag == TAG_PAIR {
                    print!(" ");
                    scheme_write(HEAP[rest.as_rib()].car);
                    rest = HEAP[rest.as_rib()].cdr;
                }
                if rest != Val::NIL {
                    print!(" . ");
                    scheme_write(rest);
                }
                print!(")");
            } else if rib.tag == TAG_STR {
                print!("{}", '"');
                let mut chars = rib.car;
                while chars != Val::NIL && !chars.is_fixnum() {
                    let cp = HEAP[chars.as_rib()].car.as_fixnum().unwrap_or(0);
                    let ch = cp as u8 as char;
                    match ch {
                        '"' => print!("\\{}", '"'),
                        '\\' => print!("\\\\"),
                        '\n' => print!("\\n"),
                        _ => print!("{ch}"),
                    }
                    chars = HEAP[chars.as_rib()].cdr;
                }
                print!("{}", '"');
            } else if rib.tag == TAG_CHAR {
                let cp = rib.car.as_fixnum().unwrap_or(0);
                print!("{}{}{}", '\x23', '\\', cp as u8 as char);
            } else if rib.tag == TAG_BOT {
                print!("{}{}", '\x23', 'f');
            } else if rib.tag == 20 {
                print!("{}{}", '\x23', 't');
            } else if rib.tag == TAG_CLS {
                print!("<procedure>");
            } else {
                print!("<rib>");
            }
        }
    }
}

// ── Vector support ──────────────────────────────────────────────

fn make_vector_fill(n: i64, fill: Val) -> Val {
    let mut elems = Val::NIL;
    for _ in 0..n { elems = cons(fill, elems); }
    unsafe {
        let idx = HEAP.len();
        HEAP.push(Rib { car: elems, cdr: Val::fixnum(n), tag: TAG_VEC });
        Val::rib(idx)
    }
}

fn is_vector(v: Val) -> bool {
    !v.is_fixnum() && v != Val::NIL && unsafe { HEAP[v.as_rib()].tag == TAG_VEC }
}

fn vector_length(v: Val) -> Val {
    if is_vector(v) { cdr(v) } else { Val::fixnum(0) }
}

fn vector_ref(v: Val, idx: i64) -> Val {
    let mut elems = car(v);
    for _ in 0..idx { elems = cdr(elems); }
    car(elems)
}

fn vector_set(v: Val, idx: i64, val: Val) {
    let mut elems = car(v);
    for _ in 0..idx { elems = cdr(elems); }
    set_car(elems, val);
}

// ── Ports / I/O ─────────────────────────────────────────────────

enum PortInner {
    Stdin(std::io::BufReader<std::io::Stdin>),
    Stdout,
    Stderr,
    FileIn(std::io::BufReader<std::fs::File>),
    FileOut(std::fs::File),
    Closed,
}

static mut PORTS: Vec<PortInner> = Vec::new();

fn make_port(port_id: i64, direction: i64) -> Val {
    unsafe {
        let idx = HEAP.len();
        HEAP.push(Rib { car: Val::fixnum(port_id), cdr: Val::fixnum(direction), tag: TAG_PORT });
        Val::rib(idx)
    }
}

fn is_port(v: Val) -> bool {
    !v.is_fixnum() && v != Val::NIL && unsafe { HEAP[v.as_rib()].tag == TAG_PORT }
}

fn port_id(v: Val) -> usize {
    car(v).as_fixnum().unwrap() as usize
}

fn port_direction(v: Val) -> i64 {
    cdr(v).as_fixnum().unwrap()
}

fn current_input_port() -> Val { make_port(0, 0) }
fn current_output_port() -> Val { make_port(1, 1) }
fn current_error_port() -> Val { make_port(2, 1) }

fn open_input_file(path: Val) -> Val {
    let s = val_to_rust_string(path);
    let file = std::fs::File::open(&s).expect("open-input-file failed");
    unsafe {
        let id = PORTS.len();
        PORTS.push(PortInner::FileIn(std::io::BufReader::new(file)));
        make_port(id as i64, 0)
    }
}

fn open_output_file(path: Val) -> Val {
    let s = val_to_rust_string(path);
    let file = std::fs::File::create(&s).expect("open-output-file failed");
    unsafe {
        let id = PORTS.len();
        PORTS.push(PortInner::FileOut(file));
        make_port(id as i64, 1)
    }
}

fn close_port(port: Val) -> Val {
    let id = port_id(port);
    unsafe { PORTS[id] = PortInner::Closed; }
    Val::NIL
}

fn read_char_port(port: Val) -> Val {
    use std::io::Read;
    let id = port_id(port);
    let mut buf = [0u8; 1];
    let n = unsafe {
        match &mut PORTS[id] {
            PortInner::Stdin(r) => r.read(&mut buf).unwrap_or(0),
            PortInner::FileIn(r) => r.read(&mut buf).unwrap_or(0),
            _ => 0,
        }
    };
    if n == 0 { EOF_VAL } else { make_char(buf[0] as i64) }
}

fn peek_char_port(port: Val) -> Val {
    use std::io::BufRead;
    let id = port_id(port);
    let byte = unsafe {
        match &mut PORTS[id] {
            PortInner::Stdin(r) => r.fill_buf().ok().and_then(|b| b.first().copied()),
            PortInner::FileIn(r) => r.fill_buf().ok().and_then(|b| b.first().copied()),
            _ => None,
        }
    };
    match byte {
        Some(b) => make_char(b as i64),
        None => EOF_VAL,
    }
}

fn write_char_port(ch: Val, port: Val) -> Val {
    use std::io::Write;
    let cp = if is_char(ch) { car(ch).as_fixnum().unwrap_or(0) } else { ch.as_fixnum().unwrap_or(0) };
    let id = port_id(port);
    unsafe {
        match &mut PORTS[id] {
            PortInner::Stdout => { print!("{}", cp as u8 as char); }
            PortInner::Stderr => { eprint!("{}", cp as u8 as char); }
            PortInner::FileOut(f) => { let _ = f.write_all(&[cp as u8]); }
            _ => {}
        }
    }
    Val::NIL
}

fn write_string_port(s: Val, port: Val) -> Val {
    use std::io::Write;
    let id = port_id(port);
    let rust_str = val_to_rust_string(s);
    unsafe {
        match &mut PORTS[id] {
            PortInner::Stdout => { print!("{rust_str}"); }
            PortInner::Stderr => { eprint!("{rust_str}"); }
            PortInner::FileOut(f) => { let _ = f.write_all(rust_str.as_bytes()); }
            _ => {}
        }
    }
    Val::NIL
}

fn read_line_port(port: Val) -> Val {
    use std::io::BufRead;
    let id = port_id(port);
    let mut line = String::new();
    let n = unsafe {
        match &mut PORTS[id] {
            PortInner::Stdin(r) => r.read_line(&mut line).unwrap_or(0),
            PortInner::FileIn(r) => r.read_line(&mut line).unwrap_or(0),
            _ => 0,
        }
    };
    if n == 0 { return EOF_VAL; }
    // Remove trailing newline
    if line.ends_with('\n') { line.pop(); }
    if line.ends_with('\r') { line.pop(); }
    rust_string_to_val(&line)
}

fn val_to_rust_string(v: Val) -> String {
    if !is_string(v) { return String::new(); }
    let mut s = String::new();
    let mut chars = car(v);
    while chars != Val::NIL && !chars.is_fixnum() {
        let cp = car(chars).as_fixnum().unwrap_or(0);
        s.push(cp as u8 as char);
        chars = cdr(chars);
    }
    s
}

fn rust_string_to_val(s: &str) -> Val {
    let len = s.len() as i64;
    let mut chars = Val::NIL;
    for b in s.bytes().rev() {
        chars = cons(Val::fixnum(b as i64), chars);
    }
    make_string(chars, Val::fixnum(len))
}

// ── Runtime read ────────────────────────────────────────────────

fn scheme_read() -> Val {
    scheme_read_port(&mut std::io::stdin().lock())
}

fn scheme_read_port(r: &mut dyn std::io::BufRead) -> Val {
    // Skip whitespace
    loop {
        let buf = match r.fill_buf() {
            Ok(b) if !b.is_empty() => b[0],
            _ => return EOF_VAL,
        };
        if buf == b' ' || buf == b'\n' || buf == b'\r' || buf == b'\t' {
            r.consume(1);
        } else {
            break;
        }
    }

    let first = {
        let buf = r.fill_buf().unwrap_or(&[]);
        if buf.is_empty() { return EOF_VAL; }
        buf[0]
    };

    match first {
        // List
        b'(' => {
            r.consume(1);
            read_list(r)
        }
        // String
        b'"' => {
            r.consume(1);
            read_string_lit(r)
        }
        // Quote
        b'\'' => {
            r.consume(1);
            let datum = scheme_read_port(r);
            // Build (quote datum)
            let q_chars = Val::NIL;
            let q_str = rust_string_to_val("quote");
            // Use a fixnum hash for the symbol (same as compiler's quoted symbols)
            let hash = "quote".bytes().fold(0i64, |acc, b| acc.wrapping_mul(31).wrapping_add(b as i64));
            let qsym = Val::fixnum(hash);
            cons(qsym, cons(datum, Val::NIL))
        }
        // Hash: #t, #f, #\char
        b'#' => {
            r.consume(1);
            let next = {
                let buf = r.fill_buf().unwrap_or(&[]);
                if buf.is_empty() { return EOF_VAL; }
                buf[0]
            };
            match next {
                b't' => { r.consume(1); skip_atom_tail(r); TRUE_VAL }
                b'f' => { r.consume(1); skip_atom_tail(r); FALSE_VAL }
                b'\\' => {
                    r.consume(1);
                    let ch = {
                        let buf = r.fill_buf().unwrap_or(&[]);
                        if buf.is_empty() { return EOF_VAL; }
                        buf[0]
                    };
                    r.consume(1);
                    // Check for named characters
                    let cp = match ch {
                        b's' | b'n' | b't' => {
                            // Peek ahead for "space", "newline", "tab"
                            let mut name = String::new();
                            name.push(ch as char);
                            loop {
                                let buf = match r.fill_buf() { Ok(b) => b, _ => break };
                                if buf.is_empty() { break; }
                                let c = buf[0];
                                if c.is_ascii_alphabetic() {
                                    name.push(c as char);
                                    r.consume(1);
                                } else { break; }
                            }
                            match name.as_str() {
                                "space" => 32,
                                "newline" => 10,
                                "tab" => 9,
                                _ => name.bytes().next().unwrap_or(0) as i64,
                            }
                        }
                        _ => ch as i64,
                    };
                    make_char(cp)
                }
                _ => EOF_VAL,
            }
        }
        // Number (possibly negative)
        b'0'..=b'9' => read_number(r, false),
        b'-' => {
            r.consume(1);
            let buf = r.fill_buf().unwrap_or(&[]);
            if !buf.is_empty() && buf[0].is_ascii_digit() {
                read_number(r, true)
            } else {
                // Symbol starting with -
                read_symbol_rest(r, "-")
            }
        }
        b'+' => {
            r.consume(1);
            let buf = r.fill_buf().unwrap_or(&[]);
            if !buf.is_empty() && buf[0].is_ascii_digit() {
                read_number(r, false)
            } else {
                read_symbol_rest(r, "+")
            }
        }
        // Symbol
        _ => {
            let mut s = String::new();
            read_symbol_into(r, &mut s);
            // Return as a fixnum hash (same encoding as compiler's quoted symbols)
            let hash = s.bytes().fold(0i64, |acc, b| acc.wrapping_mul(31).wrapping_add(b as i64));
            Val::fixnum(hash)
        }
    }
}

fn read_number(r: &mut dyn std::io::BufRead, neg: bool) -> Val {
    use std::io::BufRead;
    let mut n: i64 = 0;
    loop {
        let buf = match r.fill_buf() { Ok(b) => b, _ => break };
        if buf.is_empty() { break; }
        let c = buf[0];
        if c.is_ascii_digit() {
            n = n * 10 + (c - b'0') as i64;
            r.consume(1);
        } else {
            break;
        }
    }
    Val::fixnum(if neg { -n } else { n })
}

fn read_list(r: &mut dyn std::io::BufRead) -> Val {
    use std::io::BufRead;
    let mut items = Vec::new();
    loop {
        // Skip whitespace
        loop {
            let buf = match r.fill_buf() { Ok(b) => b, _ => return Val::NIL };
            if buf.is_empty() { return Val::NIL; }
            let c = buf[0];
            if c == b' ' || c == b'\n' || c == b'\r' || c == b'\t' {
                r.consume(1);
            } else { break; }
        }
        let buf = r.fill_buf().unwrap_or(&[]);
        if buf.is_empty() { break; }
        if buf[0] == b')' {
            r.consume(1);
            break;
        }
        items.push(scheme_read_port(r));
    }
    let mut result = Val::NIL;
    for v in items.iter().rev() {
        result = cons(*v, result);
    }
    result
}

fn read_string_lit(r: &mut dyn std::io::BufRead) -> Val {
    use std::io::BufRead;
    let mut s = String::new();
    loop {
        let buf = match r.fill_buf() { Ok(b) => b, _ => break };
        if buf.is_empty() { break; }
        let c = buf[0];
        r.consume(1);
        if c == b'"' { break; }
        if c == b'\\' {
            let buf2 = match r.fill_buf() { Ok(b) => b, _ => break };
            if !buf2.is_empty() {
                let esc = buf2[0];
                r.consume(1);
                match esc {
                    b'n' => s.push('\n'),
                    b't' => s.push('\t'),
                    b'\\' => s.push('\\'),
                    b'"' => s.push('"'),
                    _ => { s.push('\\'); s.push(esc as char); }
                }
            }
        } else {
            s.push(c as char);
        }
    }
    rust_string_to_val(&s)
}

fn read_symbol_into(r: &mut dyn std::io::BufRead, s: &mut String) {
    use std::io::BufRead;
    loop {
        let buf = match r.fill_buf() { Ok(b) => b, _ => break };
        if buf.is_empty() { break; }
        let c = buf[0];
        if c == b' ' || c == b'\n' || c == b'\r' || c == b'\t'
            || c == b'(' || c == b')' || c == b'"' || c == b';' {
            break;
        }
        s.push(c as char);
        r.consume(1);
    }
}

fn read_symbol_rest(r: &mut dyn std::io::BufRead, prefix: &str) -> Val {
    let mut s = prefix.to_string();
    read_symbol_into(r, &mut s);
    let hash = s.bytes().fold(0i64, |acc, b| acc.wrapping_mul(31).wrapping_add(b as i64));
    Val::fixnum(hash)
}

fn skip_atom_tail(r: &mut dyn std::io::BufRead) {
    use std::io::BufRead;
    loop {
        let buf = match r.fill_buf() { Ok(b) => b, _ => break };
        if buf.is_empty() { break; }
        let c = buf[0];
        if c == b' ' || c == b'\n' || c == b'\r' || c == b'\t'
            || c == b'(' || c == b')' { break; }
        r.consume(1);
    }
}
"#;

/// Compile a Scheme source string to a Rust program string.
pub fn compile(src: &str) -> String {
    let mut heap = Heap::new();
    let mut syms = SymbolTable::new();
    let exprs = crate::reader::read_all(src, &mut heap, &mut syms)
        .unwrap_or_default();
    let mut compiler = Compiler::new();
    compiler.process(exprs.as_slice(), &mut heap, &mut syms);
    compiler.emit_rust(&heap, &syms)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compile_fib() {
        let code = compile("
            (define (fib n)
              (if (< n 2) n
                  (+ (fib (- n 1)) (fib (- n 2)))))
            (display (fib 10))
            (newline)
        ");
        assert!(code.contains("fn fib("));
        assert!(code.contains("fn main()"));
        assert!(code.contains("display"));
    }

    #[test]
    fn compile_arithmetic() {
        let code = compile("(display (+ 3 4))");
        assert!(code.contains("Val::fixnum(3)"));
        assert!(code.contains("Val::fixnum(4)"));
    }

    #[test]
    fn compiled_output_compiles() {
        // Write the compiled output to a temp file and compile it with rustc
        let code = compile("
            (define (fact n)
              (if (= n 0) 1
                  (* n (fact (- n 1)))))
            (display (fact 10))
            (newline)
        ");

        let path = "/tmp/kamea_test_compiled.rs";
        std::fs::write(path, &code).unwrap();
        let output = std::process::Command::new("rustc")
            .args(["-O", "-o", "/tmp/kamea_test_compiled", path])
            .output()
            .expect("failed to run rustc");

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            panic!("rustc failed:\n{stderr}\n\nGenerated code:\n{code}");
        }

        // Run it and check output
        let run = std::process::Command::new("/tmp/kamea_test_compiled")
            .output()
            .expect("failed to run compiled program");
        let stdout = String::from_utf8_lossy(&run.stdout);
        assert_eq!(stdout.trim(), "3628800");
    }

    #[test]
    fn compiled_nqueens() {
        let code = compile("
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
            (define (nqueens n) (nqueens-count n 0 '()))
            (display (nqueens 8))
            (newline)
        ");

        let path = "/tmp/kamea_nqueens_compiled.rs";
        std::fs::write(path, &code).unwrap();
        let output = std::process::Command::new("rustc")
            .args(["-O", "-o", "/tmp/kamea_nqueens_compiled", path])
            .output()
            .expect("failed to run rustc");

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            panic!("rustc failed:\n{stderr}\n\nGenerated code:\n{code}");
        }

        let run = std::process::Command::new("/tmp/kamea_nqueens_compiled")
            .output()
            .expect("failed to run compiled program");
        let stdout = String::from_utf8_lossy(&run.stdout);
        assert_eq!(stdout.trim(), "92");
    }

    /// Helper: compile, build with rustc -O, run, return stdout
    fn compile_and_run(src: &str) -> String {
        use std::sync::atomic::{AtomicUsize, Ordering};
        static COUNTER: AtomicUsize = AtomicUsize::new(0);
        let id = COUNTER.fetch_add(1, Ordering::SeqCst);

        let code = compile(src);
        let rs_path = format!("/tmp/wispy_test_{id}.rs");
        let bin_path = format!("/tmp/wispy_test_{id}");
        std::fs::write(&rs_path, &code).unwrap();
        let output = std::process::Command::new("rustc")
            .args(["-O", "-o", &bin_path, &rs_path])
            .output()
            .expect("failed to run rustc");
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            panic!("rustc failed:\n{stderr}\n\nGenerated:\n{code}");
        }
        let run = std::process::Command::new(&bin_path)
            .output()
            .expect("failed to run");
        let _ = std::fs::remove_file(&rs_path);
        let _ = std::fs::remove_file(&bin_path);
        String::from_utf8_lossy(&run.stdout).to_string()
    }

    #[test]
    fn compiled_let_star() {
        let out = compile_and_run("
            (define (f) (let* ((x 1) (y (+ x 10))) (display y)))
            (f) (newline)
        ");
        assert_eq!(out.trim(), "11");
    }

    #[test]
    fn compiled_cond() {
        let out = compile_and_run("
            (define (classify n)
              (cond ((< n 0) 1)
                    ((= n 0) 2)
                    (else 3)))
            (display (classify (- 0 5)))
            (display (classify 0))
            (display (classify 7))
            (newline)
        ");
        assert_eq!(out.trim(), "123");
    }

    #[test]
    fn compiled_or() {
        let out = compile_and_run("
            (define (f) (or 0 0 42))
            (display (f)) (newline)
        ");
        // 0 is truthy (non-NIL fixnum), so result is 0
        assert_eq!(out.trim(), "0");
    }

    #[test]
    fn compiled_variadic_plus() {
        let out = compile_and_run("(display (+ 1 2 3 4 5)) (newline)");
        assert_eq!(out.trim(), "15");
    }

    #[test]
    fn compiled_list_ops() {
        let out = compile_and_run("
            (define (sum-list lst)
              (if (null? lst) 0
                  (+ (car lst) (sum-list (cdr lst)))))
            (display (sum-list (list 10 20 30))) (newline)
            (display (length (list 1 2 3 4 5))) (newline)
        ");
        assert_eq!(out.trim(), "60\n5");
    }

    #[test]
    fn compiled_set_bang() {
        let out = compile_and_run("
            (define (f n) (if (= n 0) 99 (f (- n 1))))
            (display (f 5)) (newline)
        ");
        assert_eq!(out.trim(), "99");
    }

    #[test]
    fn compiled_abs_max_min() {
        let out = compile_and_run("
            (display (abs -7))
            (display (max 3 9))
            (display (min 3 9))
            (newline)
        ");
        assert_eq!(out.trim(), "793");
    }

    #[test]
    fn compiled_predicates() {
        let out = compile_and_run("
            (define (show x) (display (if x 1 0)))
            (show (null? '()))
            (show (pair? (cons 1 2)))
            (show (number? 5))
            (show (zero? 0))
            (show (positive? 5))
            (newline)
        ");
        assert_eq!(out.trim(), "11111");
    }

    #[test]
    fn compiled_do_loop() {
        let out = compile_and_run("
            (define (sum-1-to-10)
              (do ((i 1 (+ i 1))
                   (sum 0 (+ sum i)))
                  ((> i 10) sum)))
            (display (sum-1-to-10)) (newline)
        ");
        assert_eq!(out.trim(), "55");
    }

    #[test]
    fn compiled_gcd() {
        let out = compile_and_run("
            (display (gcd 12 8)) (newline)
        ");
        assert_eq!(out.trim(), "4");
    }

    #[test]
    fn compiled_display_list() {
        let out = compile_and_run("
            (display (list 1 2 3)) (newline)
        ");
        assert_eq!(out.trim(), "(1 2 3)");
    }

    #[test]
    fn compiled_reverse() {
        let out = compile_and_run("
            (display (reverse (list 1 2 3))) (newline)
        ");
        assert_eq!(out.trim(), "(3 2 1)");
    }

    #[test]
    fn compiled_append() {
        let out = compile_and_run("
            (display (append (list 1 2) (list 3 4))) (newline)
        ");
        assert_eq!(out.trim(), "(1 2 3 4)");
    }

    #[test]
    fn compiled_eq() {
        let out = compile_and_run("
            (define (f) (if (eq? 1 1) 10 20))
            (display (f)) (newline)
        ");
        assert_eq!(out.trim(), "10");
    }

    // ── Algebra extension round-trip tests ────────────

    #[test]
    fn compiled_algebra_dot() {
        let out = compile_and_run("
            (display (dot CAR T_PAIR)) (newline)
            (display (dot CAR T_STR)) (newline)
        ");
        let lines: Vec<&str> = out.trim().lines().collect();
        assert_eq!(lines[0], format!("{}", table::T_PAIR));
        assert_eq!(lines[1], format!("{}", table::BOT));
    }

    #[test]
    fn compiled_algebra_tau() {
        let out = compile_and_run("
            (display (tau (cons 1 2))) (newline)
            (display (tau '())) (newline)
        ");
        let lines: Vec<&str> = out.trim().lines().collect();
        assert_eq!(lines[0], format!("{}", table::T_PAIR));
        assert_eq!(lines[1], format!("{}", table::TOP));
    }

    #[test]
    fn compiled_algebra_type_valid() {
        let out = compile_and_run("
            (display (if (type-valid? CAR T_PAIR) 1 0))
            (display (if (type-valid? CAR T_STR) 1 0))
            (newline)
        ");
        assert_eq!(out.trim(), "10");
    }

    #[test]
    fn compiled_algebra_constants() {
        let out = compile_and_run("
            (display TOP) (display BOT) (display T_PAIR) (display Y) (newline)
        ");
        assert_eq!(
            out.trim(),
            format!("{}{}{}{}", table::TOP, table::BOT, table::T_PAIR, table::Y)
        );
    }

    #[test]
    fn compiled_algebra_retraction() {
        let out = compile_and_run("
            (display (dot E (dot Q CAR))) (newline)
            (display CAR) (newline)
        ");
        let lines: Vec<&str> = out.trim().lines().collect();
        assert_eq!(lines[0], lines[1]);
    }

    #[test]
    fn compiled_algebra_user_dispatcher() {
        let out = compile_and_run("
            (define (type-dispatch x)
              (let ((t (tau x)))
                (cond ((= t T_PAIR) 1)
                      (else 0))))
            (display (type-dispatch (cons 1 2)))
            (display (type-dispatch '()))
            (newline)
        ");
        assert_eq!(out.trim(), "10");
    }

    // ── Closure tests ────────────────────────────────

    #[test]
    fn compiled_closure_basic() {
        let out = compile_and_run("
            (define (make-adder n) (lambda (x) (+ x n)))
            (define add10 (make-adder 10))
            (display (add10 32))
            (newline)
        ");
        assert_eq!(out.trim(), "42");
    }

    #[test]
    fn compiled_closure_as_arg() {
        let out = compile_and_run("
            (define (apply-twice f x) (f (f x)))
            (define (add1 x) (+ x 1))
            (display (apply-twice add1 5))
            (newline)
        ");
        assert_eq!(out.trim(), "7");
    }

    #[test]
    fn compiled_closure_lambda_arg() {
        let out = compile_and_run("
            (define (apply-twice f x) (f (f x)))
            (display (apply-twice (lambda (x) (* x 2)) 3))
            (newline)
        ");
        assert_eq!(out.trim(), "12");
    }

    #[test]
    fn compiled_closure_nested() {
        let out = compile_and_run("
            (define (make-adder n) (lambda (x) (+ x n)))
            (define (apply-it f x) (f x))
            (display (apply-it (make-adder 100) 23))
            (newline)
        ");
        assert_eq!(out.trim(), "123");
    }

    #[test]
    fn compiled_closure_map() {
        let out = compile_and_run("
            (define (map f lst)
              (if (null? lst) '()
                  (cons (f (car lst)) (map f (cdr lst)))))
            (display (map (lambda (x) (* x x)) (list 1 2 3 4)))
            (newline)
        ");
        assert_eq!(out.trim(), "(1 4 9 16)");
    }

    #[test]
    fn compiled_closure_let_lambda() {
        let out = compile_and_run("
            (define (go)
              (let ((f (lambda (x) (* x 2))))
                (display (f 21))))
            (go)
            (newline)
        ");
        assert_eq!(out.trim(), "42");
    }

    #[test]
    fn compiled_closure_immediate_lambda() {
        let out = compile_and_run("
            (display ((lambda (x y) (+ x y)) 13 29))
            (newline)
        ");
        assert_eq!(out.trim(), "42");
    }

    // ── String / char tests ────────────────────────────

    #[test]
    fn compiled_string_display() {
        let out = compile_and_run(r#"
            (display "hello")
            (newline)
        "#);
        assert_eq!(out.trim(), "hello");
    }

    #[test]
    fn compiled_string_length() {
        let out = compile_and_run(r#"
            (display (string-length "hello"))
            (newline)
        "#);
        assert_eq!(out.trim(), "5");
    }

    #[test]
    fn compiled_string_append() {
        let out = compile_and_run(r#"
            (display (string-append "he" "llo"))
            (newline)
        "#);
        assert_eq!(out.trim(), "hello");
    }

    #[test]
    fn compiled_string_equality() {
        let out = compile_and_run(r#"
            (display (if (string=? "abc" "abc") 1 0))
            (display (if (string=? "abc" "def") 1 0))
            (newline)
        "#);
        assert_eq!(out.trim(), "10");
    }

    #[test]
    fn compiled_char_display() {
        let out = compile_and_run(r#"
            (display #\A)
            (newline)
        "#);
        assert_eq!(out.trim(), "A");
    }

    #[test]
    fn compiled_string_in_list() {
        let out = compile_and_run(r#"
            (display (list "a" "b" "c"))
            (newline)
        "#);
        assert_eq!(out.trim(), "(a b c)");
    }

    #[test]
    fn compiled_string_mixed() {
        let out = compile_and_run(r#"
            (define (greet name)
              (display (string-append "Hello, " (string-append name "!"))))
            (greet "world")
            (newline)
            (display (string-length "test"))
            (newline)
        "#);
        assert_eq!(out.trim(), "Hello, world!\n4");
    }

    // ── TCO tests ────────────────────────────────

    #[test]
    fn compiled_tco_simple() {
        let out = compile_and_run("
            (define (loop n) (if (= n 0) 0 (loop (- n 1))))
            (display (loop 1000000))
            (newline)
        ");
        assert_eq!(out.trim(), "0");
    }

    #[test]
    fn compiled_tco_accumulator() {
        let out = compile_and_run("
            (define (sum n acc) (if (= n 0) acc (sum (- n 1) (+ acc n))))
            (display (sum 100000 0))
            (newline)
        ");
        // sum of 1..100000 = 100000 * 100001 / 2 = 5000050000
        assert_eq!(out.trim(), "5000050000");
    }

    #[test]
    fn compiled_tco_fib_iter() {
        let out = compile_and_run("
            (define (fib n a b) (if (= n 0) a (fib (- n 1) b (+ a b))))
            (display (fib 50 0 1))
            (newline)
        ");
        assert_eq!(out.trim(), "12586269025");
    }

    #[test]
    fn compiled_tco_through_cond() {
        let out = compile_and_run("
            (define (classify n)
              (cond ((= n 0) 0)
                    ((> n 0) (classify (- n 1)))
                    (else 99)))
            (display (classify 500000))
            (newline)
        ");
        assert_eq!(out.trim(), "0");
    }

    #[test]
    fn compiled_tco_through_let() {
        let out = compile_and_run("
            (define (count n)
              (let ((m (- n 1)))
                (if (= m 0) 42
                    (count m))))
            (display (count 500000))
            (newline)
        ");
        assert_eq!(out.trim(), "42");
    }

    // ── syntax-rules compiled tests ────────────────────

    #[test]
    fn compiled_syntax_rules_basic() {
        let out = compile_and_run("
            (define-syntax my-when
              (syntax-rules ()
                ((my-when test body)
                 (if test body 0))))
            (define (f x) (my-when (> x 0) (* x 2)))
            (display (f 5))
            (display (f 0))
            (newline)
        ");
        assert_eq!(out.trim(), "100");
    }

    #[test]
    fn compiled_syntax_rules_ellipsis() {
        let out = compile_and_run("
            (define-syntax my-let
              (syntax-rules ()
                ((my-let ((var init) ...) body ...)
                 ((lambda (var ...) body ...) init ...))))
            (define (f) (my-let ((x 10) (y 20)) (+ x y)))
            (display (f))
            (newline)
        ");
        assert_eq!(out.trim(), "30");
    }

    // ── char-ci / string-ci compiled tests ────────────

    #[test]
    fn compiled_char_ci() {
        let out = compile_and_run(r#"
            (define (f)
              (if (char-ci=? #\a #\A) 1 0))
            (display (f))
            (newline)
        "#);
        assert_eq!(out.trim(), "1");
    }

    #[test]
    fn compiled_string_ci() {
        let out = compile_and_run(r#"
            (define (f)
              (if (string-ci=? "Hello" "hello") 1 0))
            (display (f))
            (newline)
        "#);
        assert_eq!(out.trim(), "1");
    }

    #[test]
    fn compiled_char_predicates_full() {
        let out = compile_and_run(r#"
            (define (show x) (display (if x 1 0)))
            (show (char-alphabetic? #\a))
            (show (char-numeric? #\5))
            (show (char-whitespace? #\space))
            (show (char-upper-case? #\A))
            (show (char-lower-case? #\z))
            (newline)
        "#);
        assert_eq!(out.trim(), "11111");
    }

    #[test]
    fn compiled_char_case_conversion() {
        let out = compile_and_run(r#"
            (display (char->integer (char-upcase #\a)))
            (display (char->integer (char-downcase #\A)))
            (newline)
        "#);
        // 'A' = 65, 'a' = 97
        assert_eq!(out.trim(), "6597");
    }
}
