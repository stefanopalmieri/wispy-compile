# 64-Element Table Design

## Overview

64 elements, 6 bits each, stored as bytes. The 64×64 Cayley table is
4,096 bytes. Each entry specifies the result of applying element `a`
(row) to element `b` (column).

## Element Allocation

### Algebraic Core (0-6): Computational Primitives

These embed the proven Ψ structure. The sub-algebra on these 7 elements
preserves the independence properties (S, D, H).

| Idx | Name | Role | R4RS mapping |
|-----|------|------|--------------|
| 0   | ⊤    | Top absorber, empty list | `'()` / nil |
| 1   | ⊥    | Bottom absorber, false | `#f` |
| 2   | Q    | Quote / encoder | `quote` |
| 3   | E    | Eval / decoder | `eval` |
| 4   | CAR  | First projection | `car` |
| 5   | CDR  | Second projection | `cdr` |
| 6   | CONS | Pair constructor | `cons` |

### Control (7-9): Evaluation Machinery

| Idx | Name | Role |
|-----|------|------|
| 7   | ρ    | Branch / conditional dispatch |
| 8   | APPLY | Explicit application |
| 9   | CC   | call/cc marker |

### Classifier and Composition (10-11)

| Idx | Name | Role |
|-----|------|------|
| 10  | τ    | Classifier / type predicate |
| 11  | η    | Composition (cdr-through-branch) |

### Type Tags (12-17): First-Class Type Markers

These elements, when applied to a value, construct a typed reference.
When the classifier τ is applied to a typed value, the result is the
type tag. This makes `pair?`, `symbol?`, etc. single table lookups.

| Idx | Name | Type |
|-----|------|------|
| 12  | T_PAIR | pair |
| 13  | T_SYM  | symbol |
| 14  | T_CHAR | character |
| 15  | T_VEC  | vector |
| 16  | T_STR  | string |
| 17  | T_CLS  | closure / procedure |

### Immediate Fixnums (18-49): 0 through 31

32 immediate integer values. Arithmetic on these values (when the result
is also in range) is a single table lookup.

| Idx | Value |
|-----|-------|
| 18  | 0     |
| 19  | 1     |
| ... | ...   |
| 49  | 31    |

### Built-in Symbols (50-57)

8 built-in symbols that appear as immediate values. The symbol table
maps these to their string representations.

| Idx | Symbol |
|-----|--------|
| 50  | lambda |
| 51  | if     |
| 52  | define |
| 53  | quote  |
| 54  | set!   |
| 55  | begin  |
| 56  | cond   |
| 57  | else   |

### Special Values (58-61)

| Idx | Name | R4RS value |
|-----|------|------------|
| 58  | TRUE | `#t` |
| 59  | EOF  | eof-object |
| 60  | VOID | void (unspecified) |
| 61  | TAIL | tail-call marker |

### Reserved (62-63)

Available for future use or extensions.

## Design Invariants

1. **Absorber law.** Row 0 (⊤) is all zeros. Row 1 (⊥) is all ones.
   These are the left absorbers, same as Ψ₁₆.

2. **Extensionality.** All 64 rows are distinct.

3. **Retraction pair.** E(Q(x)) = x and Q(E(x)) = x on the core
   (non-absorber elements). Same as Ψ₁₆.

4. **Classifier dichotomy.** τ applied to any non-absorber produces
   either ⊤ or ⊥ (boolean) or a type tag. This extends the Ψ₁₆
   dichotomy to the R4RS type system.

5. **Type dispatch.** For any operator F and type tag T:
   `F · (T-tagged value)` is determined by the table entry for F's row
   at the column corresponding to T. Type errors return ⊥.

6. **Fixnum closure.** If a, b are immediate fixnums and a+b ≤ 31,
   then the table entry for +(a, b) is the fixnum element a+b.
   Overflow maps to a heap-allocated bignum reference.

## Table Structure

The table has natural block structure:

```
         Core  Ctrl  Tags  Fixnums    Syms  Spc  Rsv
Core     [sub-algebra]  [dispatch]  [arith]  ...
Ctrl     [eval rules]   [control]   ...
Tags     [constructors] [tag ops]   ...
Fixnums  [arith results across all fixnum pairs]
Syms     [symbol ops]
Spc      [special handling]
```

The upper-left 12×12 block is the computational core, analogous to the
full Ψ₁₆ table. The fixnum block (32×32 = 1024 entries) handles
immediate arithmetic. The remaining blocks handle type dispatch and
cross-type operations.

## Verification Strategy

1. **Sub-algebra embedding.** Prove that elements 0-11 satisfy the
   same axioms as the Ψ₁₆ core (absorbers, extensionality, retraction,
   classifier dichotomy, ICP).

2. **Type safety.** Prove that type-dispatched operations return
   correctly typed results or ⊥ (never a wrong-type result).

3. **Fixnum correctness.** Prove that immediate fixnum arithmetic
   agrees with integer arithmetic for in-range results.

4. **All by `native_decide`.** 4096 entries is well within Lean's
   `native_decide` capacity.
