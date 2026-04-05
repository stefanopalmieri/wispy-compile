//! Value representation.
//!
//! A `Val` is a 64-bit value. The low 6 bits identify the algebraic
//! element (0-63). For immediate values (fixnums, booleans, nil, symbols),
//! the upper bits are zero. For heap references (pairs, vectors, strings,
//! closures), the upper bits hold the heap index.
//!
//! Layout:
//!   Bits 0-5:   element index (0-63)
//!   Bits 6-7:   reserved (GC flags on embedded)
//!   Bits 8-63:  heap index (0 for immediates)

use crate::table;

/// A Scheme value.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Val(i64);

impl Val {
    // ── Constructors ─────────────────────────────────────────────

    /// Nil / empty list.
    pub const NIL: Val = Val(table::TOP as i64);

    /// Boolean false.
    pub const FALSE: Val = Val(table::BOT as i64);

    /// Boolean true.
    pub const TRUE: Val = Val(table::TRUE as i64);

    /// EOF object.
    pub const EOF: Val = Val(table::EOF as i64);

    /// Void (unspecified).
    pub const VOID: Val = Val(table::VOID as i64);

    /// Immediate fixnum (0-31).
    #[inline(always)]
    pub const fn fixnum(n: i64) -> Val {
        Val(table::FIXNUM_BASE as i64 + n)
    }

    /// Heap-allocated pair reference.
    #[inline(always)]
    pub const fn pair_ref(idx: usize) -> Val {
        Val(table::T_PAIR as i64 | ((idx as i64) << 8))
    }

    /// Heap-allocated symbol reference.
    #[inline(always)]
    pub const fn sym_ref(idx: usize) -> Val {
        Val(table::T_SYM as i64 | ((idx as i64) << 8))
    }

    /// Heap-allocated vector reference.
    #[inline(always)]
    pub const fn vec_ref(idx: usize) -> Val {
        Val(table::T_VEC as i64 | ((idx as i64) << 8))
    }

    /// Heap-allocated string reference.
    #[inline(always)]
    pub const fn str_ref(idx: usize) -> Val {
        Val(table::T_STR as i64 | ((idx as i64) << 8))
    }

    /// Heap-allocated closure reference.
    #[inline(always)]
    pub const fn closure_ref(idx: usize) -> Val {
        Val(table::T_CLS as i64 | ((idx as i64) << 8))
    }

    /// Character (immediate if codepoint fits, else heap).
    #[inline(always)]
    pub const fn character(cp: u32) -> Val {
        Val(table::T_CHAR as i64 | ((cp as i64) << 8))
    }

    // ── Accessors ────────────────────────────────────────────────

    /// The 6-bit element index.
    #[inline(always)]
    pub const fn elem(self) -> u8 {
        (self.0 & 0x3F) as u8
    }

    /// The heap index (upper bits), or 0 for immediates.
    #[inline(always)]
    pub const fn heap_idx(self) -> usize {
        (self.0 >> 8) as usize
    }

    /// Raw i64 representation.
    #[inline(always)]
    pub const fn raw(self) -> i64 {
        self.0
    }

    // ── Type predicates ──────────────────────────────────────────

    #[inline(always)]
    pub const fn is_nil(self) -> bool { self.elem() == table::TOP }

    #[inline(always)]
    pub const fn is_false(self) -> bool { self.elem() == table::BOT }

    #[inline(always)]
    pub const fn is_true_value(self) -> bool { !self.is_false() && !self.is_nil() }

    #[inline(always)]
    pub const fn is_boolean(self) -> bool { self.is_false() || self.elem() == table::TRUE }

    #[inline(always)]
    pub const fn is_fixnum(self) -> bool {
        self.elem() >= table::FIXNUM_BASE
            && self.elem() < table::FIXNUM_BASE + table::FIXNUM_COUNT
    }

    #[inline(always)]
    pub const fn is_pair(self) -> bool { self.elem() == table::T_PAIR }

    #[inline(always)]
    pub const fn is_symbol(self) -> bool { self.elem() == table::T_SYM }

    #[inline(always)]
    pub const fn is_char(self) -> bool { self.elem() == table::T_CHAR }

    #[inline(always)]
    pub const fn is_vector(self) -> bool { self.elem() == table::T_VEC }

    #[inline(always)]
    pub const fn is_string(self) -> bool { self.elem() == table::T_STR }

    #[inline(always)]
    pub const fn is_closure(self) -> bool { self.elem() == table::T_CLS }

    // ── Fixnum operations ────────────────────────────────────────

    /// Extract the fixnum value (0-31), or None.
    #[inline(always)]
    pub const fn as_fixnum(self) -> Option<i64> {
        if self.is_fixnum() {
            Some((self.elem() - table::FIXNUM_BASE) as i64)
        } else {
            None
        }
    }

    /// Extract the character codepoint.
    #[inline(always)]
    pub const fn as_char(self) -> Option<u32> {
        if self.is_char() {
            Some(self.heap_idx() as u32)
        } else {
            None
        }
    }

    // ── Algebraic operation ──────────────────────────────────────

    /// Apply this value to another via the Cayley table.
    /// Only meaningful for element-level operations (type dispatch,
    /// immediate fixnum arithmetic, classifier).
    #[inline(always)]
    pub fn dot(self, other: Val) -> Val {
        Val(table::dot(self.elem(), other.elem()) as i64)
    }
}

impl core::fmt::Debug for Val {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.is_nil() {
            write!(f, "()")
        } else if self.is_false() {
            write!(f, "#f")
        } else if self.elem() == table::TRUE {
            write!(f, "#t")
        } else if let Some(n) = self.as_fixnum() {
            write!(f, "{n}")
        } else if self.is_pair() {
            write!(f, "<pair@{}>", self.heap_idx())
        } else if self.is_symbol() {
            write!(f, "<sym@{}>", self.heap_idx())
        } else if let Some(cp) = self.as_char() {
            if let Some(c) = char::from_u32(cp) {
                write!(f, "#\\{c}")
            } else {
                write!(f, "#\\x{cp:04X}")
            }
        } else if self.is_vector() {
            write!(f, "<vec@{}>", self.heap_idx())
        } else if self.is_string() {
            write!(f, "<str@{}>", self.heap_idx())
        } else if self.is_closure() {
            write!(f, "<closure@{}>", self.heap_idx())
        } else {
            write!(f, "<elem:{}>", self.elem())
        }
    }
}
