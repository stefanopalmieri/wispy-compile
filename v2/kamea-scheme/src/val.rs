//! Value representation.
//!
//! Val = tagged word. Either a fixnum (tag bit set) or a rib index.
//!
//! Layout (64-bit):
//!   Bit 0:      tag (1 = fixnum, 0 = rib index)
//!   Bits 1-63:  fixnum value (signed) or rib heap index
//!
//! This is the same tagged-pointer scheme used by Ribbit, Chibi, and
//! most small Scheme implementations.

/// A Scheme value: either a fixnum or a rib reference.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Val(pub i64);

const FIXNUM_TAG: i64 = 1;

impl Val {
    // ── Constants ────────────────────────────────────────────────

    /// Nil / empty list. Rib index 0 is reserved as the nil rib.
    pub const NIL: Val = Val(0);

    // ── Constructors ─────────────────────────────────────────────

    /// Create a fixnum value.
    #[inline(always)]
    pub const fn fixnum(n: i64) -> Val {
        Val((n << 1) | FIXNUM_TAG)
    }

    /// Create a rib reference (index into the rib heap).
    #[inline(always)]
    pub const fn rib(idx: usize) -> Val {
        Val((idx as i64) << 1)
    }

    // ── Predicates ───────────────────────────────────────────────

    #[inline(always)]
    pub const fn is_fixnum(self) -> bool {
        (self.0 & FIXNUM_TAG) != 0
    }

    #[inline(always)]
    pub const fn is_rib(self) -> bool {
        (self.0 & FIXNUM_TAG) == 0
    }

    // ── Accessors ────────────────────────────────────────────────

    /// Extract the fixnum value, or None.
    #[inline(always)]
    pub const fn as_fixnum(self) -> Option<i64> {
        if self.is_fixnum() {
            Some(self.0 >> 1)
        } else {
            None
        }
    }

    /// Extract the rib index, or None.
    #[inline(always)]
    pub const fn as_rib(self) -> Option<usize> {
        if self.is_rib() {
            Some((self.0 >> 1) as usize)
        } else {
            None
        }
    }
}

impl core::fmt::Debug for Val {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if let Some(n) = self.as_fixnum() {
            write!(f, "{n}")
        } else if *self == Val::NIL {
            write!(f, "nil")
        } else {
            write!(f, "rib@{}", self.as_rib().unwrap())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixnum_roundtrip() {
        for n in [-100, -1, 0, 1, 42, 1000000] {
            let v = Val::fixnum(n);
            assert!(v.is_fixnum());
            assert!(!v.is_rib());
            assert_eq!(v.as_fixnum(), Some(n));
        }
    }

    #[test]
    fn rib_roundtrip() {
        for idx in [0, 1, 100, 65535] {
            let v = Val::rib(idx);
            assert!(v.is_rib());
            assert!(!v.is_fixnum());
            assert_eq!(v.as_rib(), Some(idx));
        }
    }

    #[test]
    fn nil_is_rib_zero() {
        assert!(Val::NIL.is_rib());
        assert_eq!(Val::NIL.as_rib(), Some(0));
    }
}
