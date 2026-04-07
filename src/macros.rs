//! syntax-rules macro expansion.
//!
//! Implements R5RS/R7RS pattern-based macros (unhygienic).
//! Supports: pattern variables, ellipsis (`...`), literals,
//! wildcards (`_`), dotted tail patterns (`(a b . rest)`).

use crate::heap::Heap;
use crate::symbol::SymbolTable;
use crate::val::Val;

/// A single syntax-rules rule: pattern → template.
#[derive(Clone)]
pub struct SyntaxRule {
    pub pattern: Val,
    pub template: Val,
}

/// A syntax-rules macro.
#[derive(Clone)]
pub struct Macro {
    pub literals: Vec<Val>,
    pub rules: Vec<SyntaxRule>,
}

/// A pattern variable binding: name → value (or list of values for ellipsis).
#[derive(Clone, Debug)]
enum Binding {
    One(Val),
    Many(Vec<Val>),
}

/// Parse a (syntax-rules (literals...) (pat tmpl) ...) form into a Macro.
pub fn parse_syntax_rules(expr: Val, heap: &Heap, syms: &SymbolTable) -> Option<Macro> {
    // expr = (syntax-rules (lit...) (pat tmpl) ...)
    if !heap.is_pair(expr) { return None; }
    let head = heap.car(expr);
    if !heap.is_symbol(head) { return None; }
    if syms.symbol_name(head)? != "syntax-rules" { return None; }

    let rest = heap.cdr(expr);
    // Parse literals list
    let lit_list = heap.car(rest);
    let mut literals = Vec::new();
    let mut l = lit_list;
    while heap.is_pair(l) {
        literals.push(heap.car(l));
        l = heap.cdr(l);
    }

    // Parse rules
    let mut rules = Vec::new();
    let mut r = heap.cdr(rest);
    while heap.is_pair(r) {
        let rule = heap.car(r);
        if heap.is_pair(rule) {
            let pattern = heap.car(rule);
            let template = heap.car(heap.cdr(rule));
            rules.push(SyntaxRule { pattern, template });
        }
        r = heap.cdr(r);
    }

    Some(Macro { literals, rules })
}

/// Try to expand a macro application. Returns Some(expanded) or None.
pub fn expand_macro(mac: &Macro, form: Val, heap: &mut Heap, syms: &SymbolTable) -> Option<Val> {
    let ellipsis = syms.symbol_name_lookup("...");

    for rule in &mac.rules {
        let mut bindings = Vec::new();
        if match_pattern(rule.pattern, form, &mac.literals, ellipsis, heap, syms, &mut bindings) {
            return Some(instantiate_template(rule.template, &bindings, ellipsis, heap, syms));
        }
    }
    None
}

/// Check if a symbol is the ellipsis `...`.
fn is_ellipsis(v: Val, ellipsis: Option<Val>) -> bool {
    match ellipsis {
        Some(e) => v == e,
        None => false,
    }
}

/// Check if a symbol is in the literals list.
fn is_literal(v: Val, literals: &[Val]) -> bool {
    literals.iter().any(|&lit| lit == v)
}

/// Check if the next element in a pattern list is `...`.
fn next_is_ellipsis(rest: Val, heap: &Heap, ellipsis: Option<Val>) -> bool {
    if !heap.is_pair(rest) { return false; }
    let next = heap.car(rest);
    heap.is_symbol(next) && is_ellipsis(next, ellipsis)
}

/// Pattern matching. Returns true if `form` matches `pattern`, populating `bindings`.
fn match_pattern(
    pattern: Val, form: Val,
    literals: &[Val], ellipsis: Option<Val>,
    heap: &Heap, syms: &SymbolTable,
    bindings: &mut Vec<(Val, Binding)>,
) -> bool {
    // NIL matches NIL
    if pattern == Val::NIL {
        return form == Val::NIL;
    }

    // Fixnum literal matches itself
    if pattern.is_fixnum() {
        return pattern == form;
    }

    // Symbol pattern
    if heap.is_symbol(pattern) {
        let name = syms.symbol_name(pattern).unwrap_or("");
        // Underscore/wildcard
        if name == "_" {
            return true;
        }
        // Ellipsis symbol shouldn't appear here
        if is_ellipsis(pattern, ellipsis) {
            return true;
        }
        // Literal: must match exactly
        if is_literal(pattern, literals) {
            return heap.is_symbol(form) && form == pattern;
        }
        // Pattern variable: bind
        bindings.push((pattern, Binding::One(form)));
        return true;
    }

    // Pair pattern
    if heap.is_pair(pattern) {
        return match_pattern_list(pattern, form, literals, ellipsis, heap, syms, bindings);
    }

    // Other (string, char, etc.): exact match
    pattern == form
}

/// Match a pattern list against a form list, handling ellipsis.
fn match_pattern_list(
    mut pattern: Val, mut form: Val,
    literals: &[Val], ellipsis: Option<Val>,
    heap: &Heap, syms: &SymbolTable,
    bindings: &mut Vec<(Val, Binding)>,
) -> bool {
    while heap.is_pair(pattern) {
        let pat_elem = heap.car(pattern);
        let pat_rest = heap.cdr(pattern);

        // Check if this element is followed by `...`
        if next_is_ellipsis(pat_rest, heap, ellipsis) {
            // Ellipsis: match zero or more of pat_elem
            // Skip past the `...` in the pattern
            let after_ellipsis = heap.cdr(pat_rest);

            // Count how many fixed elements remain after the ellipsis
            let fixed_after = list_len(after_ellipsis, heap);
            let form_remaining = list_len(form, heap);

            let to_match = if form_remaining >= fixed_after {
                form_remaining - fixed_after
            } else {
                0
            };

            // Collect pattern variables in pat_elem
            let mut ellipsis_var_names = Vec::new();
            collect_pattern_vars(pat_elem, literals, ellipsis, heap, syms, &mut ellipsis_var_names);

            // Initialize empty collections for each variable
            let mut collections: Vec<(Val, Vec<Val>)> = ellipsis_var_names.iter()
                .map(|&v| (v, Vec::new()))
                .collect();

            // Match each form element against pat_elem
            for _ in 0..to_match {
                if !heap.is_pair(form) { return false; }
                let elem = heap.car(form);
                let mut sub_bindings = Vec::new();
                if !match_pattern(pat_elem, elem, literals, ellipsis, heap, syms, &mut sub_bindings) {
                    return false;
                }
                // Collect each sub-binding into the collections
                for (name, binding) in &sub_bindings {
                    if let Binding::One(val) = binding {
                        for (cn, cv) in collections.iter_mut() {
                            if *cn == *name {
                                cv.push(*val);
                            }
                        }
                    }
                }
                form = heap.cdr(form);
            }

            // Add collected bindings as Many
            for (name, vals) in collections {
                bindings.push((name, Binding::Many(vals)));
            }

            // Continue matching after the ellipsis
            pattern = after_ellipsis;
            continue;
        }

        // No ellipsis: match one element
        if !heap.is_pair(form) { return false; }
        let form_elem = heap.car(form);
        if !match_pattern(pat_elem, form_elem, literals, ellipsis, heap, syms, bindings) {
            return false;
        }
        pattern = pat_rest;
        form = heap.cdr(form);
    }

    // Dotted tail pattern: (a b . rest) — bind rest to remaining form
    if heap.is_symbol(pattern) {
        let name = syms.symbol_name(pattern).unwrap_or("");
        if name != "_" && !is_ellipsis(pattern, ellipsis) && !is_literal(pattern, literals) {
            bindings.push((pattern, Binding::One(form)));
        }
        return true;
    }

    // Both should be exhausted (or pattern is NIL)
    pattern == Val::NIL && (form == Val::NIL || !heap.is_pair(form))
}

/// Collect all pattern variable names from a pattern element.
fn collect_pattern_vars(
    pattern: Val, literals: &[Val], ellipsis: Option<Val>,
    heap: &Heap, syms: &SymbolTable,
    vars: &mut Vec<Val>,
) {
    if heap.is_symbol(pattern) {
        let name = syms.symbol_name(pattern).unwrap_or("");
        if name == "_" { return; }
        if is_ellipsis(pattern, ellipsis) { return; }
        if is_literal(pattern, literals) { return; }
        if !vars.contains(&pattern) {
            vars.push(pattern);
        }
        return;
    }
    if heap.is_pair(pattern) {
        let mut p = pattern;
        while heap.is_pair(p) {
            let elem = heap.car(p);
            if !(heap.is_symbol(elem) && is_ellipsis(elem, ellipsis)) {
                collect_pattern_vars(elem, literals, ellipsis, heap, syms, vars);
            }
            p = heap.cdr(p);
        }
        // Dotted tail: (a b . rest) — rest is a pattern variable
        if heap.is_symbol(p) {
            let name = syms.symbol_name(p).unwrap_or("");
            if name != "_" && !is_ellipsis(p, ellipsis) && !is_literal(p, literals) {
                if !vars.contains(&p) {
                    vars.push(p);
                }
            }
        }
    }
}

/// Count the length of a proper list.
fn list_len(mut list: Val, heap: &Heap) -> usize {
    let mut n = 0;
    while heap.is_pair(list) {
        n += 1;
        list = heap.cdr(list);
    }
    n
}

/// Look up a binding by pattern variable name.
fn find_binding<'a>(name: Val, bindings: &'a [(Val, Binding)]) -> Option<&'a Binding> {
    // Search in reverse order so later bindings shadow earlier ones
    bindings.iter().rev().find(|(n, _)| *n == name).map(|(_, b)| b)
}

/// Instantiate a template with bindings.
fn instantiate_template(
    template: Val,
    bindings: &[(Val, Binding)],
    ellipsis: Option<Val>,
    heap: &mut Heap,
    syms: &SymbolTable,
) -> Val {
    // Symbol: look up binding
    if heap.is_symbol(template) {
        let name = syms.symbol_name(template).unwrap_or("");
        if name == "_" { return template; }
        if is_ellipsis(template, ellipsis) { return template; }
        if let Some(binding) = find_binding(template, bindings) {
            match binding {
                Binding::One(val) => return *val,
                Binding::Many(vals) => {
                    // Shouldn't happen without ellipsis; return first or NIL
                    return vals.first().copied().unwrap_or(Val::NIL);
                }
            }
        }
        return template; // unbound — pass through (e.g., if, begin, lambda)
    }

    // Fixnum, NIL, non-pair: return as-is
    if !heap.is_pair(template) {
        return template;
    }

    // Pair: instantiate, handling ellipsis
    instantiate_list(template, bindings, ellipsis, heap, syms)
}

/// Instantiate a template list, handling ellipsis repetition.
fn instantiate_list(
    mut template: Val,
    bindings: &[(Val, Binding)],
    ellipsis: Option<Val>,
    heap: &mut Heap,
    syms: &SymbolTable,
) -> Val {
    let mut result_parts: Vec<Val> = Vec::new();

    while heap.is_pair(template) {
        let elem = heap.car(template);
        let rest = heap.cdr(template);

        // Check if this element is followed by `...`
        if next_is_ellipsis(rest, heap, ellipsis) {
            // Ellipsis repetition: find the ellipsis variable(s) and repeat
            let mut ellipsis_vars = Vec::new();
            collect_template_vars(elem, ellipsis, heap, syms, &mut ellipsis_vars);

            // Find the number of repetitions from any Many binding
            let rep_count = ellipsis_vars.iter()
                .filter_map(|&v| {
                    find_binding(v, bindings).and_then(|b| match b {
                        Binding::Many(vals) => Some(vals.len()),
                        _ => None,
                    })
                })
                .next()
                .unwrap_or(0);

            // For each repetition, create sub-bindings with One values
            for i in 0..rep_count {
                let mut sub_bindings: Vec<(Val, Binding)> = bindings.to_vec();
                for &var in &ellipsis_vars {
                    if let Some(Binding::Many(vals)) = find_binding(var, bindings) {
                        if i < vals.len() {
                            sub_bindings.push((var, Binding::One(vals[i])));
                        }
                    }
                }
                result_parts.push(instantiate_template(elem, &sub_bindings, ellipsis, heap, syms));
            }

            // Skip past the `...`
            template = heap.cdr(rest);
            continue;
        }

        // Normal element
        result_parts.push(instantiate_template(elem, bindings, ellipsis, heap, syms));
        template = rest;
    }

    // Build the result list (handle dotted pairs if template ends with non-NIL)
    let tail = if template == Val::NIL {
        Val::NIL
    } else {
        instantiate_template(template, bindings, ellipsis, heap, syms)
    };

    let mut result = tail;
    for val in result_parts.iter().rev() {
        result = heap.cons(*val, result);
    }
    result
}

/// Collect template variable names that have Many bindings (for ellipsis repetition).
fn collect_template_vars(
    template: Val, ellipsis: Option<Val>,
    heap: &Heap, syms: &SymbolTable,
    vars: &mut Vec<Val>,
) {
    if heap.is_symbol(template) {
        if !is_ellipsis(template, ellipsis) && !vars.contains(&template) {
            vars.push(template);
        }
        return;
    }
    if heap.is_pair(template) {
        let mut p = template;
        while heap.is_pair(p) {
            let elem = heap.car(p);
            collect_template_vars(elem, ellipsis, heap, syms, vars);
            p = heap.cdr(p);
        }
        // Dotted tail
        if heap.is_symbol(p) && !is_ellipsis(p, ellipsis) && !vars.contains(&p) {
            vars.push(p);
        }
    }
}
