//! Scheme → Lua compiler.
//!
//! Compiles Scheme source into a standalone Lua program.
//! Same architecture as compile.rs but targeting Lua syntax.
//!
//! Handles: define, lambda, if, cond, let, let*, letrec, begin,
//! and/or, quote, set!, arithmetic, list ops, tail calls.

use crate::heap::Heap;
use crate::symbol::SymbolTable;
use crate::val::Val;
use crate::table;

use std::cell::{Cell, RefCell};
use std::collections::HashSet;

/// A lambda that has been lifted to a top-level function.
#[derive(Clone)]
struct LiftedLambda {
    id: usize,
    params: Vec<String>,
    free_vars: Vec<String>,
    body_list: Val,
}

/// TCO context for the function currently being compiled.
#[derive(Clone)]
struct TcoContext {
    fn_name: String,
    params: Vec<String>,
}

/// Compiler state.
pub struct LuaCompiler {
    functions: Vec<(String, Vec<String>, Val)>,
    main_exprs: Vec<Val>,
    globals: Vec<(String, Val)>,
    lifted: RefCell<Vec<LiftedLambda>>,
    next_lambda_id: Cell<usize>,
    tco: RefCell<Option<TcoContext>>,
}

impl LuaCompiler {
    pub fn new() -> Self {
        LuaCompiler {
            functions: Vec::new(),
            main_exprs: Vec::new(),
            globals: Vec::new(),
            lifted: RefCell::new(Vec::new()),
            next_lambda_id: Cell::new(0),
            tco: RefCell::new(None),
        }
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
                        if name == "load" {
                            // Compile-time file inclusion
                            let rest = heap.cdr(expr);
                            let path_val = heap.car(rest);
                            if heap.tag(path_val) == crate::table::T_STR {
                                let mut path_chars = Vec::new();
                                let mut chars = heap.rib_car(path_val);
                                while heap.is_pair(chars) {
                                    if let Some(cp) = heap.car(chars).as_fixnum() {
                                        path_chars.push(cp as u8 as char);
                                    }
                                    chars = heap.cdr(chars);
                                }
                                let path: String = path_chars.into_iter().collect();
                                if let Ok(src) = std::fs::read_to_string(&path) {
                                    let loaded = crate::reader::read_all(&src, heap, syms)
                                        .unwrap_or_default();
                                    self.process(loaded.as_slice(), heap, syms);
                                }
                            }
                            continue;
                        }
                        if name == "define" {
                            let expanded = self.expand_all(expr, &macros, heap, syms);
                            self.process_define(expanded, heap, syms);
                            continue;
                        }
                    }
                }
            }
            let expanded = self.expand_all(expr, &macros, heap, syms);
            self.main_exprs.push(expanded);
        }
    }

    fn expand_all(&self, expr: Val, macros: &[(Val, crate::macros::Macro)],
                  heap: &mut Heap, syms: &SymbolTable) -> Val {
        if !heap.is_pair(expr) { return expr; }
        let head = heap.car(expr);
        if heap.is_symbol(head) {
            let mac = macros.iter().find(|(n, _)| *n == head).map(|(_, m)| m);
            if let Some(mac) = mac {
                if let Some(expanded) = crate::macros::expand_macro(mac, expr, heap, syms) {
                    return self.expand_all(expanded, macros, heap, syms);
                }
            }
        }
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
        let mut result = list;
        for v in items.iter().rev() {
            result = heap.cons(*v, result);
        }
        result
    }

    fn process_define(&mut self, expr: Val, heap: &mut Heap, syms: &mut SymbolTable) {
        let rest = heap.cdr(expr);
        let target = heap.car(rest);

        if heap.is_symbol(target) {
            let name = syms.symbol_name(target).unwrap_or("_").to_string();
            let init = heap.car(heap.cdr(rest));
            self.globals.push((name, init));
        } else if heap.is_pair(target) {
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
            let body_list = heap.cdr(rest);
            let body = if heap.cdr(body_list) == Val::NIL {
                heap.car(body_list)
            } else {
                // Wrap multi-body in (begin ...)
                let begin_sym = syms.intern("begin", heap);
                heap.cons(begin_sym, body_list)
            };
            self.functions.push((name, params, body));
        }
    }

    // ── TCO helpers ────────────────────────────────────────────────

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
                let alt = heap.car(heap.cdr(heap.cdr(rest)));
                self.has_self_tail_call(conseq, fn_name, heap, syms)
                    || self.has_self_tail_call(alt, fn_name, heap, syms)
            }
            "begin" => self.has_self_tail_call_in_begin(rest, fn_name, heap, syms),
            "let" | "let*" | "letrec" => {
                let body = heap.cdr(rest);
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

    fn has_self_tail_call_in_begin(&self, mut list: Val, fn_name: &str,
                                    heap: &Heap, syms: &SymbolTable) -> bool {
        let mut last = Val::NIL;
        while heap.is_pair(list) {
            last = heap.car(list);
            list = heap.cdr(list);
        }
        self.has_self_tail_call(last, fn_name, heap, syms)
    }

    /// Check if an expression already produces a Lua boolean (no is_true wrapper needed).
    fn is_boolean_expr(&self, expr: Val, heap: &Heap, syms: &SymbolTable) -> bool {
        if !heap.is_pair(expr) {
            // A literal #t or #f
            let tag = heap.tag(expr);
            return tag == table::TRUE || tag == table::BOT;
        }
        let head = heap.car(expr);
        if !heap.is_symbol(head) { return false; }
        let name = syms.symbol_name(head).unwrap_or("");
        matches!(name,
            "<" | ">" | "<=" | ">=" | "=" |
            "null?" | "pair?" | "number?" | "integer?" | "boolean?" |
            "zero?" | "positive?" | "negative?" | "even?" | "odd?" |
            "eq?" | "eqv?" | "not" | "and" | "or"
        )
    }

    fn is_known_function(&self, name: &str) -> bool {
        self.functions.iter().any(|(n, _, _)| n == name)
    }

    fn function_closure_id(&self, name: &str) -> Option<usize> {
        self.functions.iter().position(|(n, _, _)| n == name)
    }

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
            "and" | "or" | "do" | "define" | "set!" | "lambda" | "quote" |
            "dot" | "tau" | "type-valid?" | "strict-mode" | "permissive-mode" |
            "TOP" | "BOT" | "Q" | "E" | "CAR" | "CDR" | "CONS" | "RHO" |
            "APPLY" | "CC" | "TAU" | "Y" |
            "T_PAIR" | "T_SYM" | "T_CLS" | "T_STR" | "T_VEC" | "T_CHAR" |
            "T_CONT" | "T_PORT" | "TRUE" | "EOF" | "VOID"
        )
    }

    // ── Free variable analysis ────────────────────────────────────

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
                    let mut p = params_list;
                    while heap.is_pair(p) {
                        if let Some(pname) = syms.symbol_name(heap.car(p)) {
                            new_bound.insert(pname.to_string());
                        }
                        p = heap.cdr(p);
                    }
                    self.walk_free_vars_list(body_exprs, heap, syms, &new_bound, fv, seen);
                }
                "let" => {
                    let bindings = heap.car(rest);
                    let body = heap.cdr(rest);
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
                    self.walk_free_vars_list(body, heap, syms, &new_bound, fv, seen);
                }
                _ => {
                    self.walk_free_vars(head, heap, syms, bound, fv, seen);
                    self.walk_free_vars_list(rest, heap, syms, bound, fv, seen);
                }
            }
        } else {
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

    fn compile_lambda(&self, rest: Val, heap: &Heap, syms: &SymbolTable) -> String {
        let params_list = heap.car(rest);
        let body_exprs = heap.cdr(rest);
        let mut params = Vec::new();
        let mut p = params_list;
        while heap.is_pair(p) {
            if let Some(pname) = syms.symbol_name(heap.car(p)) {
                params.push(pname.to_string());
            }
            p = heap.cdr(p);
        }

        // Check for free variables
        let mut bound: HashSet<String> = params.iter().cloned().collect();
        let mut fv = Vec::new();
        let mut seen = HashSet::new();
        self.walk_free_vars_list(body_exprs, heap, syms, &bound, &mut fv, &mut seen);

        if fv.is_empty() {
            // Simple lambda — inline as Lua closure
            let lua_params: Vec<String> = params.iter().map(|p| lua_ident(p)).collect();
            let body_code = self.emit_begin_inline(body_exprs, heap, syms);
            format!("function({}) return {} end", lua_params.join(", "), body_code)
        } else {
            // Lambda with free vars — Lua closures capture automatically
            let lua_params: Vec<String> = params.iter().map(|p| lua_ident(p)).collect();
            let body_code = self.emit_begin_inline(body_exprs, heap, syms);
            format!("function({}) return {} end", lua_params.join(", "), body_code)
        }
    }

    // ── Lua code generation ───────────────────────────────────────

    pub fn emit_lua(&self, heap: &Heap, syms: &SymbolTable) -> String {
        self.next_lambda_id.set(self.functions.len());

        let mut out = String::new();
        out.push_str("-- Generated by wispy-scheme compiler (Lua target)\n\n");

        // Cayley table (1-indexed for Lua)
        out.push_str("-- 32x32 Cayley table (1KB)\n");
        out.push_str("local CAYLEY = {\n");
        for i in 0..table::N {
            out.push_str("  {");
            for j in 0..table::N {
                if j > 0 { out.push_str(","); }
                out.push_str(&format!("{}", table::CAYLEY[i][j]));
            }
            out.push_str("},\n");
        }
        out.push_str("}\n\n");

        // Algebra element constants
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
            ("TRUE", table::TRUE), ("EOF_", table::EOF), ("VOID", table::VOID),
        ];
        for (name, val) in elements {
            out.push_str(&format!("local {name} = {}\n", *val));
        }
        out.push_str("\n");

        // Runtime
        out.push_str(LUA_RUNTIME);
        out.push_str("\n");

        // Forward-declare globals (so functions can reference them via set!)
        if !self.globals.is_empty() {
            let names: Vec<String> = self.globals.iter()
                .map(|(name, _)| lua_ident(name))
                .collect();
            out.push_str(&format!("local {}\n\n", names.join(", ")));
        }

        // Functions
        for (name, params, body) in &self.functions {
            let lname = lua_ident(name);
            let needs_tco = self.has_self_tail_call(*body, name, heap, syms);
            let lparams: Vec<String> = params.iter().map(|p| lua_ident(p)).collect();
            let params_str = lparams.join(", ");

            if needs_tco {
                out.push_str(&format!("function {lname}({params_str})\n"));
                out.push_str("  while true do\n");
                *self.tco.borrow_mut() = Some(TcoContext {
                    fn_name: name.clone(),
                    params: params.clone(),
                });
                let body_code = self.emit_expr(*body, heap, syms, 2);
                out.push_str(&body_code);
                *self.tco.borrow_mut() = None;
                out.push_str("  end\n");
                out.push_str("end\n\n");
            } else {
                out.push_str(&format!("function {lname}({params_str})\n"));
                let body_code = self.emit_expr(*body, heap, syms, 1);
                out.push_str(&body_code);
                out.push_str("end\n\n");
            }
        }

        // Initialize globals (already forward-declared above)
        for (name, init) in &self.globals {
            let lname = lua_ident(name);
            let init_code = self.emit_expr_inline(init.clone(), heap, syms);
            out.push_str(&format!("{lname} = {init_code}\n"));
        }

        // Main expressions — wrap in dummy local to make any expression a valid statement
        for &expr in &self.main_exprs {
            let code = self.emit_expr_inline(expr, heap, syms);
            // Use `local _ = expr` to make any expression a valid Lua statement
            // and avoid the ambiguity of (expr)(...) across lines
            out.push_str(&format!("local _ = {code}\n"));
        }

        out
    }

    /// Emit an expression in tail position.
    fn emit_expr(&self, expr: Val, heap: &Heap, syms: &SymbolTable, indent: usize) -> String {
        let pad = "  ".repeat(indent);

        if !heap.is_pair(expr) || heap.tag(expr) != table::T_PAIR {
            let code = self.emit_expr_inline(expr, heap, syms);
            return self.lua_return(&pad, &code);
        }

        let head = heap.car(expr);
        let rest = heap.cdr(expr);

        if heap.is_symbol(head) {
            let name = syms.symbol_name(head).unwrap_or("");
            match name {
                "if" => {
                    let test = heap.car(rest);
                    let rest2 = heap.cdr(rest);
                    let conseq = heap.car(rest2);
                    let alt = heap.car(heap.cdr(rest2));
                    let test_code = self.emit_expr_inline(test, heap, syms);
                    let t_code = self.emit_expr(conseq, heap, syms, indent + 1);
                    let f_code = self.emit_expr(alt, heap, syms, indent + 1);
                    let cond = if self.is_boolean_expr(test, heap, syms) {
                        test_code
                    } else {
                        format!("is_true({test_code})")
                    };
                    return format!(
                        "{pad}if {cond} then\n{t_code}{pad}else\n{f_code}{pad}end\n"
                    );
                }
                "begin" => {
                    return self.emit_begin(rest, heap, syms, indent);
                }
                "let" | "let*" => {
                    let bindings = heap.car(rest);
                    let body = heap.cdr(rest);
                    let mut out = String::new();
                    let mut b = bindings;
                    while heap.is_pair(b) {
                        let binding = heap.car(b);
                        let var = heap.car(binding);
                        let init = heap.car(heap.cdr(binding));
                        let vname = syms.symbol_name(var).unwrap_or("_");
                        let init_code = self.emit_expr_inline(init, heap, syms);
                        out.push_str(&format!("{pad}local {} = {}\n",
                            lua_ident(vname), init_code));
                        b = heap.cdr(b);
                    }
                    out.push_str(&self.emit_begin(body, heap, syms, indent));
                    return out;
                }
                "letrec" => {
                    let bindings = heap.car(rest);
                    let body = heap.cdr(rest);
                    let mut out = String::new();
                    // Declare all as local nil
                    let mut b = bindings;
                    while heap.is_pair(b) {
                        let binding = heap.car(b);
                        let var = heap.car(binding);
                        let vname = syms.symbol_name(var).unwrap_or("_");
                        out.push_str(&format!("{pad}local {}\n", lua_ident(vname)));
                        b = heap.cdr(b);
                    }
                    // Assign
                    b = bindings;
                    while heap.is_pair(b) {
                        let binding = heap.car(b);
                        let var = heap.car(binding);
                        let init = heap.car(heap.cdr(binding));
                        let vname = syms.symbol_name(var).unwrap_or("_");
                        let init_code = self.emit_expr_inline(init, heap, syms);
                        out.push_str(&format!("{pad}{} = {}\n",
                            lua_ident(vname), init_code));
                        b = heap.cdr(b);
                    }
                    out.push_str(&self.emit_begin(body, heap, syms, indent));
                    return out;
                }
                "cond" => {
                    return self.emit_cond(rest, heap, syms, indent);
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
                        // Compute all args first (temps)
                        for (i, arg) in args.iter().enumerate() {
                            out.push_str(&format!("{pad}local __t{i} = {arg}\n"));
                        }
                        for (i, p) in params.iter().enumerate() {
                            out.push_str(&format!("{pad}{} = __t{i}\n", lua_ident(p)));
                        }
                        // continue → go back to while true do
                        return out;
                    }

                    let code = self.emit_expr_inline(expr, heap, syms);
                    return self.lua_return(&pad, &code);
                }
            }
        }

        let code = self.emit_expr_inline(expr, heap, syms);
        self.lua_return(&pad, &code)
    }

    fn lua_return(&self, pad: &str, expr_code: &str) -> String {
        if self.tco.borrow().is_some() {
            format!("{pad}return {expr_code}\n")
        } else {
            format!("{pad}return {expr_code}\n")
        }
    }

    /// Emit an expression as an inline Lua expression.
    fn emit_expr_inline(&self, expr: Val, heap: &Heap, syms: &SymbolTable) -> String {
        if expr.is_fixnum() {
            return format!("{}", expr.as_fixnum().unwrap());
        }
        if expr == Val::NIL {
            return "NIL".to_string();
        }
        if !expr.is_rib() {
            return "NIL".to_string();
        }
        let tag = heap.tag(expr);
        if tag == table::T_SYM {
            let name = syms.symbol_name(expr).unwrap_or("_");
            return lua_ident(name);
        }
        if tag == table::TRUE {
            return "true".to_string();
        }
        if tag == table::BOT {
            return "false".to_string();
        }
        if tag == table::T_STR {
            // Extract string characters from the rib
            let mut chars = Vec::new();
            let mut cl = heap.rib_car(expr);
            while heap.is_pair(cl) {
                if let Some(cp) = heap.car(cl).as_fixnum() {
                    chars.push(cp as u8 as char);
                }
                cl = heap.cdr(cl);
            }
            let s: String = chars.into_iter().collect();
            return format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\"").replace('\n', "\\n"));
        }
        if tag != table::T_PAIR {
            return "NIL".to_string();
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
                    let chain = args.join(&format!(" {op} "));
                    return format!("({chain})");
                }
                "-" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    if heap.cdr(rest) == Val::NIL {
                        return format!("(-{a})");
                    }
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("({a} - {b})");
                }
                "/" | "quotient" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    // Integer division in Lua 5.3+
                    return format!("({a} // {b})");
                }
                "remainder" | "modulo" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("({a} % {b})");
                }
                "=" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("({a} == {b})");
                }
                "<" | ">" | "<=" | ">=" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("({a} {name} {b})");
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
                    let test_expr = heap.car(rest);
                    let test = self.emit_expr_inline(test_expr, heap, syms);
                    let r2 = heap.cdr(rest);
                    let c = self.emit_expr_inline(heap.car(r2), heap, syms);
                    let a = self.emit_expr_inline(heap.car(heap.cdr(r2)), heap, syms);
                    let cond = if self.is_boolean_expr(test_expr, heap, syms) {
                        test
                    } else {
                        format!("is_true({test})")
                    };
                    return format!("({cond} and ({c}) or ({a}))");
                }
                "null?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("({a} == NIL)");
                }
                "pair?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("is_pair({a})");
                }
                "number?" | "integer?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("(type({a}) == \"number\")");
                }
                "boolean?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("(type({a}) == \"boolean\")");
                }
                "string?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("(type({a}) == \"string\")");
                }
                "char?" => {
                    // Chars are not a distinct type in our Lua representation
                    return "false".to_string();
                }
                "symbol?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("is_symbol({a})");
                }
                "zero?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("({a} == 0)");
                }
                "positive?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("({a} > 0)");
                }
                "negative?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("({a} < 0)");
                }
                "even?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("({a} % 2 == 0)");
                }
                "odd?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("({a} % 2 ~= 0)");
                }
                "not" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("(not is_true({a}))");
                }
                "eq?" | "eqv?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("scm_eq({a}, {b})");
                }
                "equal?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("scm_equal({a}, {b})");
                }
                "abs" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("math.abs({a})");
                }
                "max" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("math.max({a}, {b})");
                }
                "min" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("math.min({a}, {b})");
                }
                "length" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("list_length({a})");
                }
                "list" => {
                    let mut args = Vec::new();
                    let mut r = rest;
                    while heap.is_pair(r) {
                        args.push(self.emit_expr_inline(heap.car(r), heap, syms));
                        r = heap.cdr(r);
                    }
                    let mut s = "NIL".to_string();
                    for arg in args.iter().rev() {
                        s = format!("cons({arg}, {s})");
                    }
                    return s;
                }
                "list-ref" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("list_ref({a}, {b})");
                }
                "list-tail" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("list_tail({a}, {b})");
                }
                "append" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("list_append({a}, {b})");
                }
                "reverse" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("list_reverse({a})");
                }
                "display" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("scm_display({a})");
                }
                "newline" => {
                    return "scm_newline()".to_string();
                }
                "and" => {
                    let mut parts = Vec::new();
                    let mut r = rest;
                    while heap.is_pair(r) {
                        parts.push(self.emit_expr_inline(heap.car(r), heap, syms));
                        r = heap.cdr(r);
                    }
                    if parts.is_empty() { return "true".to_string(); }
                    if parts.len() == 1 { return parts[0].clone(); }
                    // Lua `and` short-circuits and returns the last truthy value
                    return parts.join(" and ");
                }
                "or" => {
                    let mut parts = Vec::new();
                    let mut r = rest;
                    while heap.is_pair(r) {
                        parts.push(self.emit_expr_inline(heap.car(r), heap, syms));
                        r = heap.cdr(r);
                    }
                    if parts.is_empty() { return "false".to_string(); }
                    if parts.len() == 1 { return parts[0].clone(); }
                    return parts.join(" or ");
                }
                "set!" => {
                    let var = heap.car(rest);
                    let val = heap.car(heap.cdr(rest));
                    let vname = syms.symbol_name(var).unwrap_or("_");
                    let val_code = self.emit_expr_inline(val, heap, syms);
                    return format!("(function() {} = {}; return NIL end)()", lua_ident(vname), val_code);
                }
                // Control-flow forms as inline expressions (IIFE wrappers)
                "let" | "let*" => {
                    let bindings = heap.car(rest);
                    let body = heap.cdr(rest);
                    let mut parts = String::from("(function() ");
                    let mut b = bindings;
                    while heap.is_pair(b) {
                        let binding = heap.car(b);
                        let var = heap.car(binding);
                        let init = heap.car(heap.cdr(binding));
                        let vname = syms.symbol_name(var).unwrap_or("_");
                        let init_code = self.emit_expr_inline(init, heap, syms);
                        parts.push_str(&format!("local {} = {}; ", lua_ident(vname), init_code));
                        b = heap.cdr(b);
                    }
                    parts.push_str(&self.emit_iife_body(body, heap, syms));
                    parts.push_str(" end)()");
                    return parts;
                }
                "letrec" => {
                    let bindings = heap.car(rest);
                    let body = heap.cdr(rest);
                    let mut parts = String::from("(function() ");
                    let mut b = bindings;
                    // Declare all
                    let mut names = Vec::new();
                    while heap.is_pair(b) {
                        let binding = heap.car(b);
                        let var = heap.car(binding);
                        let vname = syms.symbol_name(var).unwrap_or("_");
                        names.push(lua_ident(vname));
                        b = heap.cdr(b);
                    }
                    for n in &names {
                        parts.push_str(&format!("local {}; ", n));
                    }
                    // Assign
                    b = bindings;
                    for n in &names {
                        let binding = heap.car(b);
                        let init = heap.car(heap.cdr(binding));
                        let init_code = self.emit_expr_inline(init, heap, syms);
                        parts.push_str(&format!("{} = {}; ", n, init_code));
                        b = heap.cdr(b);
                    }
                    parts.push_str(&self.emit_iife_body(body, heap, syms));
                    parts.push_str(" end)()");
                    return parts;
                }
                "begin" => {
                    let mut count = 0;
                    let mut r = rest;
                    while heap.is_pair(r) { count += 1; r = heap.cdr(r); }
                    if count == 1 {
                        return self.emit_expr_inline(heap.car(rest), heap, syms);
                    }
                    let mut parts = String::from("(function() ");
                    parts.push_str(&self.emit_iife_body(rest, heap, syms));
                    parts.push_str(" end)()");
                    return parts;
                }
                "cond" => {
                    // Emit cond as nested ternary or IIFE
                    let mut parts = String::from("(function() ");
                    let mut clauses = rest;
                    let mut first = true;
                    while heap.is_pair(clauses) {
                        let clause = heap.car(clauses);
                        let test = heap.car(clause);
                        let body = heap.cdr(clause);
                        let body_code = self.emit_begin_inline(body, heap, syms);

                        if heap.is_symbol(test) && syms.sym_eq(test, "else") {
                            parts.push_str(&format!("return {} ", body_code));
                            parts.push_str("end)()");
                            return parts;
                        }

                        let test_code = self.emit_expr_inline(test, heap, syms);
                        let cond = if self.is_boolean_expr(test, heap, syms) {
                            test_code
                        } else {
                            format!("is_true({})", test_code)
                        };
                        if first {
                            parts.push_str(&format!("if {} then return {} ", cond, body_code));
                            first = false;
                        } else {
                            parts.push_str(&format!("elseif {} then return {} ", cond, body_code));
                        }
                        clauses = heap.cdr(clauses);
                    }
                    if !first {
                        parts.push_str("else return NIL end ");
                    }
                    parts.push_str("end)()");
                    return parts;
                }
                "quote" => {
                    let datum = heap.car(rest);
                    return self.emit_datum(datum, heap, syms);
                }
                "lambda" => {
                    return self.compile_lambda(rest, heap, syms);
                }
                // Algebra extension
                "dot" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    // CAYLEY is 1-indexed in Lua
                    return format!("CAYLEY[{a}+1][{b}+1]");
                }
                "tau" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    return format!("scm_tau({a})");
                }
                "type-valid?" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("(CAYLEY[{a}+1][{b}+1] ~= BOT)");
                }
                "expt" => {
                    let a = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let b = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    // Use integer result
                    return format!("(math.floor({a} ^ {b}))");
                }
                "apply" => {
                    let f = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let args = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("scm_apply({f}, {args})");
                }
                "map" => {
                    let f = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let lst = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("scm_map({f}, {lst})");
                }
                "for-each" => {
                    let f = self.emit_expr_inline(heap.car(rest), heap, syms);
                    let lst = self.emit_expr_inline(heap.car(heap.cdr(rest)), heap, syms);
                    return format!("scm_for_each({f}, {lst})");
                }
                _ => {
                    // Function call
                    let fname = lua_ident(name);
                    let mut args = Vec::new();
                    let mut a = rest;
                    while heap.is_pair(a) {
                        args.push(self.emit_expr_inline(heap.car(a), heap, syms));
                        a = heap.cdr(a);
                    }
                    return format!("{fname}({})", args.join(", "));
                }
            }
        }

        // Generic call — head is not a symbol
        {
            let head_code = self.emit_expr_inline(head, heap, syms);
            let mut args = Vec::new();
            let mut a = rest;
            while heap.is_pair(a) {
                args.push(self.emit_expr_inline(heap.car(a), heap, syms));
                a = heap.cdr(a);
            }
            format!("({head_code})({})", args.join(", "))
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
                let pad = "  ".repeat(indent);
                let semi = if code.starts_with('(') { ";" } else { "" };
                out.push_str(&format!("{pad}{semi}{code}\n"));
            }
            body = heap.cdr(body);
        }
        out
    }

    /// Emit a body list as statements inside an IIFE: all but last as statements, last as return.
    fn emit_iife_body(&self, mut body: Val, heap: &Heap, syms: &SymbolTable) -> String {
        let mut exprs = Vec::new();
        while heap.is_pair(body) {
            exprs.push(heap.car(body));
            body = heap.cdr(body);
        }
        let mut out = String::new();
        for (i, &e) in exprs.iter().enumerate() {
            let code = self.emit_expr_inline(e, heap, syms);
            if i == exprs.len() - 1 {
                out.push_str(&format!("return {}", code));
            } else {
                out.push_str(&format!("{}; ", code));
            }
        }
        out
    }

    fn emit_begin_inline(&self, mut body: Val, heap: &Heap, syms: &SymbolTable) -> String {
        // For inline lambdas — return the last expression
        let mut last = "NIL".to_string();
        while heap.is_pair(body) {
            last = self.emit_expr_inline(heap.car(body), heap, syms);
            body = heap.cdr(body);
        }
        last
    }

    fn emit_cond(&self, mut clauses: Val, heap: &Heap, syms: &SymbolTable, indent: usize) -> String {
        let pad = "  ".repeat(indent);
        let mut out = String::new();
        let mut first = true;

        while heap.is_pair(clauses) {
            let clause = heap.car(clauses);
            let test = heap.car(clause);
            let body = heap.cdr(clause);

            if heap.is_symbol(test) && syms.sym_eq(test, "else") {
                out.push_str(&format!("{pad}else\n"));
                out.push_str(&self.emit_begin(body, heap, syms, indent + 1));
                out.push_str(&format!("{pad}end\n"));
                return out;
            }

            let test_code = self.emit_expr_inline(test, heap, syms);
            let cond = if self.is_boolean_expr(test, heap, syms) {
                test_code
            } else {
                format!("is_true({test_code})")
            };
            if first {
                out.push_str(&format!("{pad}if {cond} then\n"));
                first = false;
            } else {
                out.push_str(&format!("{pad}elseif {cond} then\n"));
            }
            out.push_str(&self.emit_begin(body, heap, syms, indent + 1));
            clauses = heap.cdr(clauses);
        }

        if !first {
            out.push_str(&format!("{pad}else\n{pad}  return NIL\n{pad}end\n"));
        }
        out
    }

    fn emit_datum(&self, datum: Val, heap: &Heap, syms: &SymbolTable) -> String {
        if datum.is_fixnum() {
            return format!("{}", datum.as_fixnum().unwrap());
        }
        if datum == Val::NIL {
            return "NIL".to_string();
        }
        if heap.is_symbol(datum) {
            let name = syms.symbol_name(datum).unwrap_or("_");
            return format!("mksym(\"{}\")", name);
        }
        if heap.tag(datum) == table::TRUE {
            return "true".to_string();
        }
        if heap.tag(datum) == table::BOT {
            return "false".to_string();
        }
        if heap.tag(datum) == table::T_STR {
            let mut chars = Vec::new();
            let mut cl = heap.rib_car(datum);
            while heap.is_pair(cl) {
                if let Some(cp) = heap.car(cl).as_fixnum() {
                    chars.push(cp as u8 as char);
                }
                cl = heap.cdr(cl);
            }
            let s: String = chars.into_iter().collect();
            return format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\"").replace('\n', "\\n"));
        }
        if heap.is_pair(datum) {
            let car_code = self.emit_datum(heap.car(datum), heap, syms);
            let cdr_code = self.emit_datum(heap.cdr(datum), heap, syms);
            return format!("cons({car_code}, {cdr_code})");
        }
        "NIL".to_string()
    }
}

/// Convert a Scheme identifier to a valid Lua identifier.
fn lua_ident(name: &str) -> String {
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
    // Avoid Lua keywords
    match s.as_str() {
        "end" => "end_".to_string(),
        "then" => "then_".to_string(),
        "do" => "do_".to_string(),
        "function" => "function_".to_string(),
        "local" => "local_".to_string(),
        "return" => "return_".to_string(),
        "nil" => "nil_".to_string(),
        "true" => "true_".to_string(),
        "false" => "false_".to_string(),
        "and" => "and_".to_string(),
        "or" => "or_".to_string(),
        "not" => "not_".to_string(),
        "repeat" => "repeat_".to_string(),
        "until" => "until_".to_string(),
        "while" => "while_".to_string(),
        "for" => "for_".to_string(),
        "in" => "in_".to_string(),
        "if" => "if_".to_string(),
        "else" => "else_".to_string(),
        "elseif" => "elseif_".to_string(),
        _ => s,
    }
}

/// Minimal Lua runtime for Scheme cons cells and display.
const LUA_RUNTIME: &str = r#"
-- Sentinel for '()
local NIL = {}

-- Symbols as tagged tables
local _sym_cache = {}
function mksym(name)
  if not _sym_cache[name] then _sym_cache[name] = {__sym = name} end
  return _sym_cache[name]
end
function is_symbol(v) return type(v) == "table" and v.__sym ~= nil end
function sym_name(v) return v.__sym end

function scm_eq(a, b)
  if a == b then return true end
  if is_symbol(a) and is_symbol(b) then return a.__sym == b.__sym end
  return false
end

-- Cons cells as tables: {car, cdr}
function cons(a, b) return {a, b} end
function car(p) if type(p) == "table" and p ~= NIL then return p[1] else return NIL end end
function cdr(p) if type(p) == "table" and p ~= NIL then return p[2] else return NIL end end

function is_true(v) return v ~= false and v ~= nil end
function is_pair(v) return type(v) == "table" and v ~= NIL end

function list_length(lst)
  local n = 0
  while lst ~= NIL and type(lst) == "table" do n = n + 1; lst = lst[2] end
  return n
end

function list_ref(lst, n)
  for i = 1, n do lst = lst[2] end
  return lst[1]
end

function list_tail(lst, n)
  for i = 1, n do lst = lst[2] end
  return lst
end

function list_append(a, b)
  if a == NIL then return b end
  return cons(car(a), list_append(cdr(a), b))
end

function list_reverse(lst)
  local r = NIL
  while lst ~= NIL and type(lst) == "table" do
    r = cons(car(lst), r)
    lst = cdr(lst)
  end
  return r
end

function scm_equal(a, b)
  if a == b then return true end
  if is_symbol(a) and is_symbol(b) then return a.__sym == b.__sym end
  if type(a) == "table" and type(b) == "table" and a ~= NIL and b ~= NIL then
    if a.__sym or b.__sym then return false end
    return scm_equal(a[1], b[1]) and scm_equal(a[2], b[2])
  end
  return false
end

function scm_display(v)
  if v == NIL then io.write("()")
  elseif v == true then io.write(string.char(35) .. "t")
  elseif v == false then io.write(string.char(35) .. "f")
  elseif type(v) == "number" then io.write(tostring(v))
  elseif is_symbol(v) then io.write(v.__sym)
  elseif type(v) == "string" then io.write(v)
  elseif type(v) == "table" then
    io.write("(")
    scm_display(v[1])
    local rest = v[2]
    while rest ~= NIL and type(rest) == "table" do
      io.write(" ")
      scm_display(rest[1])
      rest = rest[2]
    end
    if rest ~= NIL then
      io.write(" . ")
      scm_display(rest)
    end
    io.write(")")
  end
end

function scm_newline() io.write("\n"); return NIL end

function scm_tau(v)
  if v == NIL then return TOP end
  if type(v) == "number" then return TOP end
  if type(v) == "boolean" then return (v and 20 or 1) end
  return TOP
end

function scm_apply(f, args)
  local a = {}
  while args ~= NIL and type(args) == "table" do
    a[#a+1] = args[1]
    args = args[2]
  end
  return f(table.unpack(a))
end

function scm_map(f, lst)
  if lst == NIL then return NIL end
  return cons(f(car(lst)), scm_map(f, cdr(lst)))
end

function scm_for_each(f, lst)
  while lst ~= NIL and type(lst) == "table" do
    f(car(lst))
    lst = cdr(lst)
  end
  return NIL
end
"#;

/// Compile a Scheme source string to a Lua program string.
pub fn compile_lua(src: &str) -> String {
    let mut heap = Heap::new();
    let mut syms = SymbolTable::new();
    let exprs = crate::reader::read_all(src, &mut heap, &mut syms)
        .unwrap_or_default();
    let mut compiler = LuaCompiler::new();
    compiler.process(exprs.as_slice(), &mut heap, &mut syms);
    compiler.emit_lua(&heap, &syms)
}
