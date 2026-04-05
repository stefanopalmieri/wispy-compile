//! Rib heap.
//!
//! Every heap object is a rib: three fields (car, cdr, tag).
//! The tag is a Cayley table element that determines the type.
//!
//! Pairs, closures, symbols, strings, vectors, continuations, ports
//! are all ribs — same struct, different tag.
//!
//! Based on Ribbit's rib model, extended with algebraic type dispatch.
//!
//! Two backends:
//! - `alloc` feature: `Vec<Rib>`, growable.
//! - no `alloc`: fixed `[Rib; HEAP_CAP]` array, bump pointer.

#[cfg(feature = "alloc")]
#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::vec::Vec;

use crate::val::Val;
use crate::table;

/// A rib: the universal heap object.
///
/// - Pair:         car=first, cdr=rest,       tag=T_PAIR
/// - Closure:      car=code,  cdr=env,        tag=T_CLS
/// - Symbol:       car=name,  cdr=value,      tag=T_SYM
/// - String:       car=chars, cdr=length,     tag=T_STR
/// - Vector:       car=elems, cdr=length,     tag=T_VEC
/// - Character:    car=codepoint, cdr=nil,    tag=T_CHAR
/// - Continuation: car=stack, cdr=pc,         tag=T_CONT
/// - Port:         car=fd,    cdr=direction,  tag=T_PORT
#[derive(Clone, Copy)]
pub struct Rib {
    pub car: Val,
    pub cdr: Val,
    pub tag: u8,
}

/// Fixed heap capacity for no_std builds (number of ribs).
#[cfg(not(feature = "alloc"))]
pub const HEAP_CAP: usize = 8192;

/// Bump-allocated rib heap.
pub struct Heap {
    #[cfg(feature = "alloc")]
    ribs: Vec<Rib>,
    #[cfg(not(feature = "alloc"))]
    ribs: [Rib; HEAP_CAP],
    #[cfg(not(feature = "alloc"))]
    len: usize,
    /// When true, type errors (car of non-pair, etc.) panic instead
    /// of silently returning NIL. Default: true. The algebra extension
    /// can set this to false for total algebraic dispatch.
    pub strict: bool,
}

impl Heap {
    const EMPTY_RIB: Rib = Rib { car: Val::NIL, cdr: Val::NIL, tag: table::TOP };

    #[cfg(feature = "alloc")]
    pub fn new() -> Self {
        let mut ribs = Vec::with_capacity(65536);
        ribs.push(Self::EMPTY_RIB); // index 0 = nil sentinel
        Heap { ribs, strict: true }
    }

    #[cfg(not(feature = "alloc"))]
    pub fn new() -> Self {
        let mut h = Heap {
            ribs: [Self::EMPTY_RIB; HEAP_CAP],
            len: 1, // index 0 = nil sentinel
            strict: true,
        };
        h.ribs[0] = Self::EMPTY_RIB;
        h
    }

    /// Reset the heap (free all allocations except nil).
    pub fn reset(&mut self) {
        #[cfg(feature = "alloc")]
        { self.ribs.truncate(1); }
        #[cfg(not(feature = "alloc"))]
        { self.len = 1; }
    }

    /// Number of allocated ribs.
    pub fn len(&self) -> usize {
        #[cfg(feature = "alloc")]
        { self.ribs.len() }
        #[cfg(not(feature = "alloc"))]
        { self.len }
    }

    // ── Allocation ───────────────────────────────────────────────

    /// Allocate a rib with the given fields and tag.
    #[inline]
    fn alloc(&mut self, car: Val, cdr: Val, tag: u8) -> Val {
        #[cfg(feature = "alloc")]
        {
            let idx = self.ribs.len();
            self.ribs.push(Rib { car, cdr, tag });
            Val::rib(idx)
        }
        #[cfg(not(feature = "alloc"))]
        {
            let idx = self.len;
            assert!(idx < HEAP_CAP, "heap overflow");
            self.ribs[idx] = Rib { car, cdr, tag };
            self.len = idx + 1;
            Val::rib(idx)
        }
    }

    /// Allocate a pair.
    #[inline]
    pub fn cons(&mut self, car: Val, cdr: Val) -> Val {
        self.alloc(car, cdr, table::T_PAIR)
    }

    /// Allocate a symbol (name = string rib, value = binding).
    #[inline]
    pub fn symbol(&mut self, name: Val, value: Val) -> Val {
        self.alloc(name, value, table::T_SYM)
    }

    /// Allocate a closure (code + environment).
    #[inline]
    pub fn closure(&mut self, code: Val, env: Val) -> Val {
        self.alloc(code, env, table::T_CLS)
    }

    /// Allocate a string (chars list + length).
    #[inline]
    pub fn string(&mut self, chars: Val, length: Val) -> Val {
        self.alloc(chars, length, table::T_STR)
    }

    /// Allocate a vector (elems list + length).
    #[inline]
    pub fn vector(&mut self, elems: Val, length: Val) -> Val {
        self.alloc(elems, length, table::T_VEC)
    }

    /// Allocate a character rib.
    #[inline]
    pub fn character(&mut self, codepoint: i64) -> Val {
        self.alloc(Val::fixnum(codepoint), Val::NIL, table::T_CHAR)
    }

    /// Allocate a continuation.
    #[inline]
    pub fn continuation(&mut self, stack: Val, pc: Val) -> Val {
        self.alloc(stack, pc, table::T_CONT)
    }

    /// Allocate a special value (#t, eof, void).
    #[inline]
    pub fn alloc_special(&mut self, tag: u8) -> Val {
        self.alloc(Val::NIL, Val::NIL, tag)
    }

    /// Allocate a rib with explicit car, cdr, and tag. Public for eval.
    #[inline]
    pub fn alloc_rib(&mut self, car: Val, cdr: Val, tag: u8) -> Val {
        self.alloc(car, cdr, tag)
    }

    /// Raw set-cdr (bypasses type dispatch). For promise caching.
    #[inline]
    pub fn set_cdr_raw(&mut self, v: Val, new_cdr: Val) {
        if v.is_rib() && v != Val::NIL {
            self.rib_mut(v).cdr = new_cdr;
        }
    }

    // ── Access ────��──────────────────────────────────────────────

    /// Get the rib at a given index.
    #[inline(always)]
    fn rib(&self, v: Val) -> &Rib {
        &self.ribs[v.as_rib().unwrap()]
    }

    /// Get a mutable rib at a given index.
    #[inline(always)]
    fn rib_mut(&mut self, v: Val) -> &mut Rib {
        &mut self.ribs[v.as_rib().unwrap()]
    }

    /// Raw car access (no type dispatch). For internal use.
    #[inline(always)]
    pub fn rib_car(&self, v: Val) -> Val {
        if v.is_rib() && v != Val::NIL {
            self.rib(v).car
        } else {
            Val::NIL
        }
    }

    /// Raw cdr access (no type dispatch). For internal use.
    #[inline(always)]
    pub fn rib_cdr(&self, v: Val) -> Val {
        if v.is_rib() && v != Val::NIL {
            self.rib(v).cdr
        } else {
            Val::NIL
        }
    }

    /// Get the tag of a value.
    /// Fixnums have no rib, so we return a synthetic marker.
    #[inline(always)]
    pub fn tag(&self, v: Val) -> u8 {
        if v.is_fixnum() {
            // Fixnums don't have ribs. Return BOT as a "not a rib" marker.
            // The classifier handles this: table[TAU][BOT] = BOT.
            table::BOT
        } else if v == Val::NIL {
            table::TOP
        } else {
            self.rib(v).tag
        }
    }

    /// car of a value. Uses the Cayley table for type dispatch.
    /// In strict mode, panics on type errors. In permissive mode, returns NIL.
    #[inline]
    pub fn car(&self, v: Val) -> Val {
        if v.is_fixnum() || v == Val::NIL {
            if self.strict { panic!("car: not a pair: {:?}", v); }
            return Val::NIL;
        }
        let tag = self.tag(v);
        if table::dot(table::CAR, tag) == table::BOT {
            if self.strict { panic!("car: not a pair (tag {})", tag); }
            Val::NIL
        } else {
            self.rib(v).car
        }
    }

    /// cdr of a value. Uses the Cayley table for type dispatch.
    /// In strict mode, panics on type errors. In permissive mode, returns NIL.
    #[inline]
    pub fn cdr(&self, v: Val) -> Val {
        if v.is_fixnum() || v == Val::NIL {
            if self.strict { panic!("cdr: not a pair: {:?}", v); }
            return Val::NIL;
        }
        let tag = self.tag(v);
        if table::dot(table::CDR, tag) == table::BOT {
            if self.strict { panic!("cdr: not a pair (tag {})", tag); }
            Val::NIL
        } else {
            self.rib(v).cdr
        }
    }

    /// set-car!
    #[inline]
    pub fn set_car(&mut self, v: Val, new_car: Val) {
        if v.is_rib() && v != Val::NIL {
            self.rib_mut(v).car = new_car;
        }
    }

    /// set-cdr!
    #[inline]
    pub fn set_cdr(&mut self, v: Val, new_cdr: Val) {
        if v.is_rib() && v != Val::NIL {
            self.rib_mut(v).cdr = new_cdr;
        }
    }

    // ── Type predicates (table-driven) ───────────────────────────

    /// Type predicate: is this value a pair?
    #[inline(always)]
    pub fn is_pair(&self, v: Val) -> bool {
        self.tag(v) == table::T_PAIR
    }

    /// Type predicate: is this value a symbol?
    #[inline(always)]
    pub fn is_symbol(&self, v: Val) -> bool {
        self.tag(v) == table::T_SYM
    }

    /// Type predicate: is this value a closure?
    #[inline(always)]
    pub fn is_closure(&self, v: Val) -> bool {
        self.tag(v) == table::T_CLS
    }

    /// Type predicate: is this value a string?
    #[inline(always)]
    pub fn is_string(&self, v: Val) -> bool {
        self.tag(v) == table::T_STR
    }

    /// Type predicate: is this value a vector?
    #[inline(always)]
    pub fn is_vector(&self, v: Val) -> bool {
        self.tag(v) == table::T_VEC
    }

    /// General type classifier: returns the table element for the type.
    /// Fixnums → BOT, nil → TOP, ribs → their tag.
    #[inline(always)]
    pub fn classify(&self, v: Val) -> u8 {
        table::dot(table::TAU, self.tag(v))
    }

    // ── List utilities ────���──────────────────────────────────────

    /// Build a list from a slice.
    pub fn list(&mut self, vals: &[Val]) -> Val {
        let mut result = Val::NIL;
        for &v in vals.iter().rev() {
            result = self.cons(v, result);
        }
        result
    }

    /// Length of a proper list.
    pub fn length(&self, mut v: Val) -> usize {
        let mut n = 0;
        while self.is_pair(v) {
            n += 1;
            v = self.cdr(v);
        }
        n
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cons_car_cdr() {
        let mut h = Heap::new();
        let p = h.cons(Val::fixnum(1), Val::fixnum(2));
        assert!(h.is_pair(p));
        assert_eq!(h.car(p), Val::fixnum(1));
        assert_eq!(h.cdr(p), Val::fixnum(2));
    }

    #[test]
    fn car_of_non_pair_is_nil() {
        let mut h = Heap::new();
        h.strict = false; // permissive mode: type errors return NIL
        let sym = h.symbol(Val::NIL, Val::NIL);
        assert_eq!(h.car(sym), Val::NIL); // type error → nil
        assert_eq!(h.car(Val::fixnum(42)), Val::NIL);
    }

    #[test]
    #[should_panic(expected = "car: not a pair")]
    fn car_of_non_pair_panics_strict() {
        let h = Heap::new(); // strict mode by default
        h.car(Val::fixnum(42)); // should panic
    }

    #[test]
    fn list_and_length() {
        let mut h = Heap::new();
        let lst = h.list(&[Val::fixnum(1), Val::fixnum(2), Val::fixnum(3)]);
        assert_eq!(h.length(lst), 3);
        assert_eq!(h.car(lst), Val::fixnum(1));
        assert_eq!(h.car(h.cdr(lst)), Val::fixnum(2));
        assert_eq!(h.car(h.cdr(h.cdr(lst))), Val::fixnum(3));
    }

    #[test]
    fn closure() {
        let mut h = Heap::new();
        let cls = h.closure(Val::fixnum(99), Val::NIL);
        assert!(h.is_closure(cls));
        assert!(!h.is_pair(cls));
        assert_eq!(h.tag(cls), table::T_CLS);
    }

    #[test]
    fn classify() {
        let mut h = Heap::new();
        let p = h.cons(Val::NIL, Val::NIL);
        assert_eq!(h.classify(p), table::T_PAIR);
        assert_eq!(h.classify(Val::NIL), table::TOP);
    }

    #[test]
    fn set_car_cdr() {
        let mut h = Heap::new();
        let p = h.cons(Val::fixnum(1), Val::fixnum(2));
        h.set_car(p, Val::fixnum(10));
        h.set_cdr(p, Val::fixnum(20));
        assert_eq!(h.car(p), Val::fixnum(10));
        assert_eq!(h.cdr(p), Val::fixnum(20));
    }

    #[test]
    fn different_rib_types() {
        let mut h = Heap::new();
        let pair = h.cons(Val::fixnum(1), Val::NIL);
        let sym = h.symbol(Val::NIL, Val::NIL);
        let cls = h.closure(Val::NIL, Val::NIL);
        let str = h.string(Val::NIL, Val::fixnum(0));
        let vec = h.vector(Val::NIL, Val::fixnum(0));
        let chr = h.character(65);

        assert_eq!(h.tag(pair), table::T_PAIR);
        assert_eq!(h.tag(sym), table::T_SYM);
        assert_eq!(h.tag(cls), table::T_CLS);
        assert_eq!(h.tag(str), table::T_STR);
        assert_eq!(h.tag(vec), table::T_VEC);
        assert_eq!(h.tag(chr), table::T_CHAR);
    }

    #[test]
    fn reset() {
        let mut h = Heap::new();
        h.cons(Val::fixnum(1), Val::NIL);
        h.cons(Val::fixnum(2), Val::NIL);
        assert_eq!(h.len(), 3); // 1 (nil) + 2 allocations
        h.reset();
        assert_eq!(h.len(), 1); // just nil
    }
}
