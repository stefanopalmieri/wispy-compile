/- # WispyScheme — 32-element Cayley table verification

   Machine verification of the 32×32 Cayley table found by Z3.
   All proofs are computational: `decide` or `native_decide`.

   Elements:
     0=⊤  1=⊥  2=Q  3=E  4=CAR  5=CDR  6=CONS  7=RHO  8=APPLY  9=CC
     10=TAU  11=Y  12=T_PAIR  13=T_SYM  14=T_CLS  15=T_STR  16=T_VEC
     17=T_CHAR  18=T_CONT  19=T_PORT  20=TRUE  21=EOF  22=VOID  23-31=reserved
-/

import Mathlib.Data.Fintype.Basic

set_option maxHeartbeats 800000

namespace WispyScheme

/-! ## Part 1: The Cayley Table -/

abbrev W := Fin 32

private def rawDot : Nat → Nat → Nat
  -- Row 0: ⊤ (absorber)
  | 0, _ => 0
  -- Row 1: ⊥ (absorber)
  | 1, _ => 1
  -- Row 2: Q
  | 2, 0 => 2 | 2, 1 => 2 | 2, 2 => 3 | 2, 3 => 2
  | 2, 4 => 11 | 2, 5 => 4 | 2, 6 => 6 | 2, 7 => 7
  | 2, 8 => 9 | 2, 9 => 5 | 2, 10 => 8 | 2, 11 => 10
  | 2, 12 => 0 | 2, 13 => 2 | 2, 14 => 2 | 2, 15 => 13
  | 2, 16 => 2 | 2, 17 => 2 | 2, 18 => 2 | 2, 19 => 2
  | 2, 20 => 2 | 2, 21 => 2 | 2, 22 => 2 | 2, 23 => 2
  | 2, 24 => 0 | 2, 25 => 2 | 2, 26 => 2 | 2, 27 => 2
  | 2, 28 => 2 | 2, 29 => 2 | 2, 30 => 2 | 2, 31 => 2
  -- Row 3: E
  | 3, 0 => 0 | 3, 1 => 1 | 3, 2 => 3 | 3, 3 => 2
  | 3, 4 => 5 | 3, 5 => 9 | 3, 6 => 6 | 3, 7 => 7
  | 3, 8 => 10 | 3, 9 => 8 | 3, 10 => 11 | 3, 11 => 4
  | 3, 12 => 0 | 3, 13 => 0 | 3, 14 => 0 | 3, 15 => 0
  | 3, 16 => 0 | 3, 17 => 0 | 3, 18 => 0 | 3, 19 => 0
  | 3, 20 => 0 | 3, 21 => 0 | 3, 22 => 0 | 3, 23 => 0
  | 3, 24 => 0 | 3, 25 => 0 | 3, 26 => 0 | 3, 27 => 0
  | 3, 28 => 0 | 3, 29 => 0 | 3, 30 => 0 | 3, 31 => 0
  -- Row 4: CAR
  | 4, 0 => 2 | 4, 1 => 0 | 4, 2 => 1 | 4, 3 => 3
  | 4, 4 => 2 | 4, 5 => 0 | 4, 6 => 10 | 4, 7 => 6
  | 4, 8 => 0 | 4, 9 => 10 | 4, 10 => 0 | 4, 11 => 23
  | 4, 12 => 12 | 4, 13 => 1 | 4, 14 => 1 | 4, 15 => 1
  | 4, 16 => 1 | 4, 17 => 1 | 4, 18 => 1 | 4, 19 => 1
  | 4, 20 => 1 | 4, 21 => 1 | 4, 22 => 1 | 4, 23 => 0
  | 4, 24 => 0 | 4, 25 => 0 | 4, 26 => 0 | 4, 27 => 0
  | 4, 28 => 0 | 4, 29 => 0 | 4, 30 => 0 | 4, 31 => 0
  -- Row 5: CDR
  | 5, 0 => 1 | 5, 1 => 2 | 5, 2 => 2 | 5, 3 => 10
  | 5, 4 => 6 | 5, 5 => 23 | 5, 6 => 10 | 5, 7 => 0
  | 5, 8 => 10 | 5, 9 => 6 | 5, 10 => 0 | 5, 11 => 6
  | 5, 12 => 12 | 5, 13 => 1 | 5, 14 => 1 | 5, 15 => 1
  | 5, 16 => 1 | 5, 17 => 1 | 5, 18 => 1 | 5, 19 => 1
  | 5, 20 => 1 | 5, 21 => 1 | 5, 22 => 1 | 5, 23 => 0
  | 5, 24 => 0 | 5, 25 => 0 | 5, 26 => 0 | 5, 27 => 0
  | 5, 28 => 0 | 5, 29 => 0 | 5, 30 => 0 | 5, 31 => 1
  -- Row 6: CONS
  | 6, 0 => 0 | 6, 1 => 2 | 6, 2 => 4 | 6, 3 => 9
  | 6, 4 => 8 | 6, 5 => 11 | 6, 6 => 9 | 6, 7 => 10
  | 6, 8 => 6 | 6, 9 => 8 | 6, 10 => 10 | 6, 11 => 7
  | 6, 12 => 2 | 6, 13 => 2 | 6, 14 => 2 | 6, 15 => 2
  | 6, 16 => 2 | 6, 17 => 2 | 6, 18 => 2 | 6, 19 => 2
  | 6, 20 => 2 | 6, 21 => 0 | 6, 22 => 2 | 6, 23 => 0
  | 6, 24 => 0 | 6, 25 => 0 | 6, 26 => 0 | 6, 27 => 3
  | 6, 28 => 0 | 6, 29 => 2 | 6, 30 => 2 | 6, 31 => 2
  -- Row 7: RHO
  | 7, 0 => 2 | 7, 1 => 2 | 7, 2 => 1 | 7, 3 => 3
  | 7, 4 => 2 | 7, 5 => 11 | 7, 6 => 10 | 7, 7 => 6
  | 7, 8 => 6 | 7, 9 => 10 | 7, 10 => 0 | 7, 11 => 23
  | 7, 12 => 2 | 7, 13 => 2 | 7, 14 => 2 | 7, 15 => 2
  | 7, 16 => 2 | 7, 17 => 31 | 7, 18 => 2 | 7, 19 => 2
  | 7, 20 => 2 | 7, 21 => 2 | 7, 22 => 2 | 7, 23 => 2
  | 7, 24 => 2 | 7, 25 => 2 | 7, 26 => 0 | 7, 27 => 0
  | 7, 28 => 0 | 7, 29 => 0 | 7, 30 => 0 | 7, 31 => 11
  -- Row 8: APPLY
  | 8, 0 => 0 | 8, 1 => 2 | 8, 2 => 4 | 8, 3 => 4
  | 8, 4 => 11 | 8, 5 => 11 | 8, 6 => 7 | 8, 7 => 2
  | 8, 8 => 2 | 8, 9 => 2 | 8, 10 => 0 | 8, 11 => 11
  | 8, 12 => 3 | 8, 13 => 2 | 8, 14 => 2 | 8, 15 => 2
  | 8, 16 => 2 | 8, 17 => 0 | 8, 18 => 2 | 8, 19 => 2
  | 8, 20 => 2 | 8, 21 => 2 | 8, 22 => 2 | 8, 23 => 2
  | 8, 24 => 0 | 8, 25 => 2 | 8, 26 => 2 | 8, 27 => 1
  | 8, 28 => 2 | 8, 29 => 0 | 8, 30 => 2 | 8, 31 => 3
  -- Row 9: CC
  | 9, 0 => 0 | 9, 1 => 3 | 9, 2 => 4 | 9, 3 => 3
  | 9, 4 => 6 | 9, 5 => 2 | 9, 6 => 2 | 9, 7 => 2
  | 9, 8 => 10 | 9, 9 => 9 | 9, 10 => 11 | 9, 11 => 11
  | 9, 12 => 4 | 9, 13 => 2 | 9, 14 => 2 | 9, 15 => 2
  | 9, 16 => 0 | 9, 17 => 2 | 9, 18 => 3 | 9, 19 => 2
  | 9, 20 => 2 | 9, 21 => 2 | 9, 22 => 2 | 9, 23 => 0
  | 9, 24 => 2 | 9, 25 => 2 | 9, 26 => 2 | 9, 27 => 0
  | 9, 28 => 0 | 9, 29 => 0 | 9, 30 => 2 | 9, 31 => 4
  -- Row 10: TAU
  | 10, 0 => 0 | 10, 1 => 1 | 10, 2 => 0 | 10, 3 => 0
  | 10, 4 => 0 | 10, 5 => 1 | 10, 6 => 0 | 10, 7 => 0
  | 10, 8 => 1 | 10, 9 => 0 | 10, 10 => 0 | 10, 11 => 0
  | 10, 12 => 12 | 10, 13 => 13 | 10, 14 => 14 | 10, 15 => 15
  | 10, 16 => 16 | 10, 17 => 17 | 10, 18 => 18 | 10, 19 => 19
  | 10, 20 => 20 | 10, 21 => 21 | 10, 22 => 22 | 10, 23 => 0
  | 10, 24 => 1 | 10, 25 => 0 | 10, 26 => 0 | 10, 27 => 0
  | 10, 28 => 0 | 10, 29 => 0 | 10, 30 => 0 | 10, 31 => 0
  -- Row 11: Y
  | 11, 0 => 2 | 11, 1 => 2 | 11, 2 => 2 | 11, 3 => 3
  | 11, 4 => 9 | 11, 5 => 11 | 11, 6 => 7 | 11, 7 => 3
  | 11, 8 => 10 | 11, 9 => 9 | 11, 10 => 2 | 11, 11 => 11
  | 11, 12 => 0 | 11, 13 => 2 | 11, 14 => 2 | 11, 15 => 2
  | 11, 16 => 2 | 11, 17 => 2 | 11, 18 => 2 | 11, 19 => 2
  | 11, 20 => 2 | 11, 21 => 2 | 11, 22 => 15 | 11, 23 => 2
  | 11, 24 => 2 | 11, 25 => 2 | 11, 26 => 0 | 11, 27 => 1
  | 11, 28 => 3 | 11, 29 => 2 | 11, 30 => 2 | 11, 31 => 5
  -- Row 12: T_PAIR
  | 12, 0 => 0 | 12, 1 => 1 | 12, _ => 12
  -- Row 13: T_SYM
  | 13, 0 => 0 | 13, 1 => 1 | 13, _ => 13
  -- Row 14: T_CLS
  | 14, 0 => 0 | 14, 1 => 1 | 14, _ => 14
  -- Row 15: T_STR
  | 15, 0 => 0 | 15, 1 => 1 | 15, _ => 15
  -- Row 16: T_VEC
  | 16, 0 => 0 | 16, 1 => 1 | 16, _ => 16
  -- Row 17: T_CHAR
  | 17, 0 => 0 | 17, 1 => 1 | 17, _ => 17
  -- Row 18: T_CONT
  | 18, 0 => 0 | 18, 1 => 1 | 18, _ => 18
  -- Row 19: T_PORT
  | 19, 0 => 0 | 19, 1 => 1 | 19, _ => 19
  -- Row 20: TRUE
  | 20, 0 => 0 | 20, 1 => 1 | 20, _ => 20
  -- Row 21: EOF
  | 21, 0 => 0 | 21, 1 => 1 | 21, _ => 21
  -- Row 22: VOID
  | 22, 0 => 0 | 22, 1 => 1 | 22, _ => 22
  -- Rows 23-31: reserved (absorber-like, first col 0, rest = row index)
  | 23, 0 => 0 | 23, _ => 23
  | 24, 0 => 0 | 24, _ => 24
  | 25, 0 => 0 | 25, _ => 25
  | 26, 0 => 0 | 26, _ => 26
  | 27, 0 => 0 | 27, _ => 27
  | 28, 0 => 0 | 28, _ => 28
  | 29, 0 => 0 | 29, _ => 29
  | 30, 0 => 0 | 30, _ => 30
  | 31, 0 => 0 | 31, _ => 31
  -- Out of range (unreachable for Fin 32)
  | _, _ => 0

private theorem rawDot_bound (a b : Fin 32) : rawDot a.val b.val < 32 := by
  revert a b; native_decide

/-- The WispyScheme binary operation on 32 elements. -/
def dot (a b : W) : W := ⟨rawDot a.val b.val, rawDot_bound a b⟩

/-! ## Part 2: Named Constants -/

abbrev TOP   : W := 0   -- ⊤
abbrev BOT   : W := 1   -- ⊥
abbrev Q     : W := 2   -- Q (quotient/encoder)
abbrev E     : W := 3   -- E (evaluator/decoder)
abbrev CAR   : W := 4   -- car
abbrev CDR   : W := 5   -- cdr
abbrev CONS  : W := 6   -- cons
abbrev RHO   : W := 7   -- ρ (branch selector)
abbrev APPLY : W := 8   -- apply
abbrev CC    : W := 9   -- call/cc
abbrev TAU   : W := 10  -- τ (type classifier)
abbrev Y     : W := 11  -- Y (fixed-point combinator)

/-! ## Part 3: Structural Axioms -/

-- 3a. Absorber ⊤
theorem absorber_top : ∀ x : W, dot TOP x = TOP := by native_decide

-- 3b. Absorber ⊥
theorem absorber_bot : ∀ x : W, dot BOT x = BOT := by native_decide

-- 3c. Extensionality
theorem extensionality : ∀ a b : W, a ≠ b →
    ∃ x : W, dot a x ≠ dot b x := by native_decide

-- 3d. E-transparency
theorem e_transparency : dot E TOP = TOP ∧ dot E BOT = BOT := by native_decide

-- 3e. Q/E retraction on core
theorem retraction_EQ : ∀ x : W, 2 ≤ x.val → x.val < 12 →
    dot E (dot Q x) = x := by native_decide

theorem retraction_QE : ∀ x : W, 2 ≤ x.val → x.val < 12 →
    dot Q (dot E x) = x := by native_decide

-- 3f. Classifier dichotomy
theorem classifier_dichotomy : ∀ x : W, 2 ≤ x.val → x.val < 12 →
    (dot TAU x = TOP ∨ dot TAU x = BOT) := by native_decide

theorem classifier_hits_top : ∃ x : W, 2 ≤ x.val ∧ x.val < 12 ∧ dot TAU x = TOP := by
  native_decide

theorem classifier_hits_bot : ∃ x : W, 2 ≤ x.val ∧ x.val < 12 ∧ dot TAU x = BOT := by
  native_decide

-- 3g. Branch
theorem branch : ∀ x : W, 2 ≤ x.val → x.val < 12 →
    (dot TAU x = TOP → dot RHO x = dot CAR x) ∧
    (dot TAU x = BOT → dot RHO x = dot CONS x) := by native_decide

-- 3h. Composition
theorem composition : ∀ x : W, 2 ≤ x.val → x.val < 12 →
    dot CDR x = dot RHO (dot CONS x) := by native_decide

-- 3i. CONS core-preserving
theorem cons_core_preserving : ∀ x : W, 2 ≤ x.val → x.val < 12 →
    2 ≤ (dot CONS x).val ∧ (dot CONS x).val < 12 := by native_decide

-- 3j. Y fixed point
theorem y_fixed_point :
    dot RHO (dot Y RHO) = dot Y RHO ∧ (dot Y RHO).val ≥ 2 := by native_decide

-- 3k. Type dispatch (car)
theorem car_pair : dot CAR 12 = 12 := by native_decide

theorem car_non_pair_bot : dot CAR 13 = BOT ∧ dot CAR 14 = BOT ∧
    dot CAR 15 = BOT ∧ dot CAR 16 = BOT ∧ dot CAR 17 = BOT ∧
    dot CAR 18 = BOT ∧ dot CAR 19 = BOT := by native_decide

-- 3l. Classifier on type tags
theorem classifier_type_tags :
    dot TAU 12 = 12 ∧ dot TAU 13 = 13 ∧ dot TAU 14 = 14 ∧
    dot TAU 15 = 15 ∧ dot TAU 16 = 16 ∧ dot TAU 17 = 17 ∧
    dot TAU 18 = 18 ∧ dot TAU 19 = 19 := by native_decide

end WispyScheme
