//! The 32×32 Cayley table (1KB).
//!
//! Every type dispatch decision is a single table lookup.
//! The table lives in `.rodata` (flash on embedded).

pub const N: usize = 32;

// ── Algebraic core (0-11) ────────────────────────────────────────

pub const TOP: u8 = 0;     // ⊤, nil, '()
pub const BOT: u8 = 1;     // ⊥, #f, type error
pub const Q: u8 = 2;       // quote / encoder
pub const E: u8 = 3;       // eval / decoder
pub const CAR: u8 = 4;     // first projection
pub const CDR: u8 = 5;     // second projection (= ρ ∘ cons)
pub const CONS: u8 = 6;    // pair constructor, core-preserving
pub const RHO: u8 = 7;     // branch (conditional dispatch)
pub const APPLY: u8 = 8;   // explicit application
pub const CC: u8 = 9;      // call/cc
pub const TAU: u8 = 10;    // classifier (type predicate)
pub const Y: u8 = 11;      // Y combinator (fixed point)

// ── R4RS type tags (12-19) ───────────────────────────────────────
// These are rib tag values. A rib with tag T_PAIR is a pair, etc.

pub const T_PAIR: u8 = 12;
pub const T_SYM: u8 = 13;
pub const T_CLS: u8 = 14;  // closure / procedure
pub const T_STR: u8 = 15;
pub const T_VEC: u8 = 16;
pub const T_CHAR: u8 = 17;
pub const T_CONT: u8 = 18; // first-class continuation
pub const T_PORT: u8 = 19;

// ── Special values (20-22) ───────────────────────────────────────

pub const TRUE: u8 = 20;   // #t
pub const EOF: u8 = 21;    // eof-object
pub const VOID: u8 = 22;   // void (unspecified)

// ── The table ────────────────────────────────────────────────────

include!("../tools/cayley_32.rs");

/// Apply element `a` to element `b` via the Cayley table.
#[inline(always)]
pub fn dot(a: u8, b: u8) -> u8 {
    CAYLEY[a as usize][b as usize]
}

#[cfg(test)]
mod tests {
    use super::*;

    const CORE: [u8; 10] = [Q, E, CAR, CDR, CONS, RHO, APPLY, CC, TAU, Y];
    const TYPE_TAGS: [u8; 8] = [T_PAIR, T_SYM, T_CLS, T_STR, T_VEC, T_CHAR, T_CONT, T_PORT];

    #[test]
    fn absorbers() {
        for j in 0..N as u8 {
            assert_eq!(dot(TOP, j), TOP);
            assert_eq!(dot(BOT, j), BOT);
        }
    }

    #[test]
    fn extensionality() {
        let mut rows: Vec<Vec<u8>> = (0..N).map(|i| CAYLEY[i].to_vec()).collect();
        rows.sort();
        rows.dedup();
        assert_eq!(rows.len(), N);
    }

    #[test]
    fn retraction_qe() {
        for &x in &CORE {
            assert_eq!(dot(E, dot(Q, x)), x, "E(Q({x}))≠{x}");
            assert_eq!(dot(Q, dot(E, x)), x, "Q(E({x}))≠{x}");
        }
    }

    #[test]
    fn e_transparency() {
        assert_eq!(dot(E, TOP), TOP);
        assert_eq!(dot(E, BOT), BOT);
    }

    #[test]
    fn classifier_core() {
        for &x in &CORE {
            let tx = dot(TAU, x);
            assert!(tx == TOP || tx == BOT, "τ({x})={tx}");
        }
    }

    #[test]
    fn classifier_type_tags() {
        for &t in &TYPE_TAGS {
            assert_eq!(dot(TAU, t), t, "τ should return type tag for type {t}");
        }
    }

    #[test]
    fn branch() {
        for &x in &CORE {
            if dot(TAU, x) == TOP {
                assert_eq!(dot(RHO, x), dot(CAR, x));
            } else {
                assert_eq!(dot(RHO, x), dot(CONS, x));
            }
        }
    }

    #[test]
    fn composition() {
        for &x in &CORE {
            assert_eq!(dot(CDR, x), dot(RHO, dot(CONS, x)));
        }
    }

    #[test]
    fn cons_core_preserving() {
        for &x in &CORE {
            let gx = dot(CONS, x);
            assert!(gx >= 2 && gx < 12, "cons({x})={gx} not in core");
        }
    }

    #[test]
    fn y_fixed_point() {
        let yp = dot(Y, RHO);
        assert!(yp >= 2);
        assert_eq!(dot(RHO, yp), yp);
    }

    #[test]
    fn car_type_dispatch() {
        assert_eq!(dot(CAR, T_PAIR), T_PAIR);
        for &t in &TYPE_TAGS {
            if t != T_PAIR {
                assert_eq!(dot(CAR, t), BOT, "car({t}) should be error");
            }
        }
    }
}
