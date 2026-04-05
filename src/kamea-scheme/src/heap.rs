//! Heap allocator for pairs, vectors, strings, and closures.
//!
//! Default: bump allocator (pointer increment, no free, no GC).
//! Call `Heap::reset()` between top-level evaluations to reclaim.
//!
//! For long-running workloads, swap in MMTk Immix behind a feature flag.

use crate::value::Val;

/// A cons cell: car and cdr.
#[derive(Clone, Copy)]
pub struct Pair {
    pub car: Val,
    pub cdr: Val,
}

/// Bump-allocated heap.
///
/// Generic over the backing store so it works with both
/// `Vec<Pair>` (std) and `&mut [Pair]` (no_std, fixed buffer).
pub struct Heap {
    pairs: [Pair; Self::MAX_PAIRS],
    pair_count: usize,
    // TODO: vector heap, string heap, closure heap
}

impl Heap {
    const MAX_PAIRS: usize = 65536;

    /// Create a new empty heap.
    pub fn new() -> Self {
        Heap {
            pairs: [Pair { car: Val::NIL, cdr: Val::NIL }; Self::MAX_PAIRS],
            pair_count: 0,
        }
    }

    /// Reset the heap (free all allocations).
    pub fn reset(&mut self) {
        self.pair_count = 0;
    }

    /// Number of live pairs.
    pub fn pair_count(&self) -> usize {
        self.pair_count
    }

    /// Allocate a new pair, returning a pair-ref Val.
    #[inline]
    pub fn cons(&mut self, car: Val, cdr: Val) -> Val {
        let idx = self.pair_count;
        if idx >= Self::MAX_PAIRS {
            panic!("kamea-scheme: pair heap overflow");
        }
        self.pairs[idx] = Pair { car, cdr };
        self.pair_count = idx + 1;
        Val::pair_ref(idx)
    }

    /// Read the car of a pair.
    #[inline(always)]
    pub fn car(&self, v: Val) -> Val {
        if !v.is_pair() { return Val::FALSE; }
        self.pairs[v.heap_idx()].car
    }

    /// Read the cdr of a pair.
    #[inline(always)]
    pub fn cdr(&self, v: Val) -> Val {
        if !v.is_pair() { return Val::FALSE; }
        self.pairs[v.heap_idx()].cdr
    }

    /// Mutate the car of a pair (set-car!).
    #[inline(always)]
    pub fn set_car(&mut self, v: Val, new_car: Val) {
        if v.is_pair() {
            self.pairs[v.heap_idx()].car = new_car;
        }
    }

    /// Mutate the cdr of a pair (set-cdr!).
    #[inline(always)]
    pub fn set_cdr(&mut self, v: Val, new_cdr: Val) {
        if v.is_pair() {
            self.pairs[v.heap_idx()].cdr = new_cdr;
        }
    }

    /// Build a list from a slice of values.
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
        while v.is_pair() {
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
        let mut heap = Heap::new();
        let pair = heap.cons(Val::fixnum(1), Val::fixnum(2));
        assert!(pair.is_pair());
        assert_eq!(heap.car(pair), Val::fixnum(1));
        assert_eq!(heap.cdr(pair), Val::fixnum(2));
    }

    #[test]
    fn list_building() {
        let mut heap = Heap::new();
        let lst = heap.list(&[Val::fixnum(1), Val::fixnum(2), Val::fixnum(3)]);
        assert_eq!(heap.length(lst), 3);
        assert_eq!(heap.car(lst), Val::fixnum(1));
        assert_eq!(heap.car(heap.cdr(lst)), Val::fixnum(2));
        assert_eq!(heap.car(heap.cdr(heap.cdr(lst))), Val::fixnum(3));
        assert!(heap.cdr(heap.cdr(heap.cdr(lst))).is_nil());
    }

    #[test]
    fn set_car_cdr() {
        let mut heap = Heap::new();
        let pair = heap.cons(Val::fixnum(1), Val::fixnum(2));
        heap.set_car(pair, Val::fixnum(10));
        heap.set_cdr(pair, Val::fixnum(20));
        assert_eq!(heap.car(pair), Val::fixnum(10));
        assert_eq!(heap.cdr(pair), Val::fixnum(20));
    }

    #[test]
    fn reset() {
        let mut heap = Heap::new();
        heap.cons(Val::fixnum(1), Val::NIL);
        heap.cons(Val::fixnum(2), Val::NIL);
        assert_eq!(heap.pair_count(), 2);
        heap.reset();
        assert_eq!(heap.pair_count(), 0);
    }
}
