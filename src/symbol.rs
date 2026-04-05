//! Symbol interning.
//!
//! All symbols with the same name share the same rib. This makes
//! symbol comparison a pointer check (`==`) instead of string comparison.
//!
//! Two backends:
//! - `alloc` feature: `Vec<(String, Val)>`.
//! - no `alloc`: fixed array of `([u8; MAX_SYM_LEN], u8, Val)` entries.

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::string::{String, ToString};
#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::vec::Vec;

use crate::heap::Heap;
use crate::val::Val;

/// Maximum length of a symbol name (no_std only).
#[cfg(not(feature = "alloc"))]
const MAX_SYM_LEN: usize = 48;

/// Maximum number of interned symbols (no_std only).
#[cfg(not(feature = "alloc"))]
const MAX_SYMS: usize = 512;

/// Shared symbol table. Thread through reader and evaluator.
pub struct SymbolTable {
    #[cfg(feature = "alloc")]
    entries: Vec<(String, Val)>,
    #[cfg(not(feature = "alloc"))]
    entries: [([u8; MAX_SYM_LEN], u8, Val); MAX_SYMS],
    #[cfg(not(feature = "alloc"))]
    len: usize,
}

impl SymbolTable {
    #[cfg(feature = "alloc")]
    pub fn new() -> Self {
        SymbolTable { entries: Vec::new() }
    }

    #[cfg(not(feature = "alloc"))]
    pub fn new() -> Self {
        SymbolTable {
            entries: [([0u8; MAX_SYM_LEN], 0, Val::NIL); MAX_SYMS],
            len: 0,
        }
    }

    /// Intern a symbol: return the existing rib if the name was seen before,
    /// otherwise allocate a new symbol rib and cache it.
    #[cfg(feature = "alloc")]
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

    #[cfg(not(feature = "alloc"))]
    pub fn intern(&mut self, name: &str, heap: &mut Heap) -> Val {
        let name_bytes = name.as_bytes();
        let name_len = name_bytes.len();
        // Look up existing entry
        for i in 0..self.len {
            let (ref buf, slen, val) = self.entries[i];
            if slen as usize == name_len && &buf[..name_len] == name_bytes {
                return val;
            }
        }
        // Allocate new entry
        let name_val = Self::make_string(name, heap);
        let sym = heap.symbol(name_val, Val::NIL);
        assert!(self.len < MAX_SYMS, "symbol table overflow");
        assert!(name_len <= MAX_SYM_LEN, "symbol name too long");
        let mut buf = [0u8; MAX_SYM_LEN];
        buf[..name_len].copy_from_slice(name_bytes);
        self.entries[self.len] = (buf, name_len as u8, sym);
        self.len += 1;
        sym
    }

    /// Get the name of a symbol by finding it in the table.
    #[cfg(feature = "alloc")]
    pub fn symbol_name(&self, sym: Val) -> Option<&str> {
        for (name, &val) in self.entries.iter().map(|(n, v)| (n, v)) {
            if val == sym {
                return Some(name);
            }
        }
        None
    }

    #[cfg(not(feature = "alloc"))]
    pub fn symbol_name(&self, sym: Val) -> Option<&str> {
        for i in 0..self.len {
            let (ref buf, slen, val) = self.entries[i];
            if val == sym {
                let name = core::str::from_utf8(&buf[..slen as usize]).ok()?;
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
