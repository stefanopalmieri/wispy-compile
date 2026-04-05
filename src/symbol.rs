//! Symbol interning.
//!
//! All symbols with the same name share the same rib. This makes
//! symbol comparison a pointer check (`==`) instead of string comparison.

use crate::heap::Heap;
use crate::val::Val;

/// Shared symbol table. Thread through reader and evaluator.
pub struct SymbolTable {
    entries: Vec<(String, Val)>,
}

impl SymbolTable {
    pub fn new() -> Self {
        SymbolTable { entries: Vec::new() }
    }

    /// Intern a symbol: return the existing rib if the name was seen before,
    /// otherwise allocate a new symbol rib and cache it.
    pub fn intern(&mut self, name: &str, heap: &mut Heap) -> Val {
        for &(ref n, v) in &self.entries {
            if n == name {
                return v;
            }
        }
        let name_val = Self::make_string(name, heap);
        let sym = heap.symbol(name_val, Val::NIL);
        self.entries.push((name.to_string(), sym));
        sym
    }

    /// Get the name of a symbol by finding it in the table.
    pub fn symbol_name(&self, sym: Val) -> Option<&str> {
        for (name, &val) in self.entries.iter().map(|(n, v)| (n, v)) {
            if val == sym {
                return Some(name);
            }
        }
        None
    }

    /// Check if a symbol has a given name.
    pub fn sym_eq(&self, sym: Val, name: &str) -> bool {
        self.symbol_name(sym) == Some(name)
    }

    fn make_string(s: &str, heap: &mut Heap) -> Val {
        let mut chars = Val::NIL;
        for &b in s.as_bytes().iter().rev() {
            chars = heap.cons(Val::fixnum(b as i64), chars);
        }
        heap.string(chars, Val::fixnum(s.len() as i64))
    }
}
