"""
table_build.py — Build the full 64×64 table from the verified 12×12 core.

Strategy:
  1. Embed the 12×12 core at indices 0-11
  2. Fixnum arithmetic block at indices 18-49 (already designed)
  3. Type dispatch: how core operators interact with type tags + fixnums
  4. Fill remaining rows to ensure extensionality (all 64 rows distinct)
  5. Emit as Rust const array
"""

from table import *

# ══════════════════════════════════════════════════════════════════
# The verified 12×12 core (from table_search.py)
# ══════════════════════════════════════════════════════════════════

CORE_TABLE = [
    [ 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0],  # ⊤
    [ 1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1],  # ⊥
    [ 0,  0,  7,  9,  8, 11, 10,  2,  6,  5,  3,  4],  # Q
    [ 0,  1,  7, 10, 11,  9,  8,  2,  4,  3,  6,  5],  # E
    [ 2,  2,  5,  2,  0,  2,  6,  8,  9,  2, 11, 11],  # car
    [ 2,  2,  0,  9,  0,  7,  9,  0, 11, 11, 11,  8],  # cdr
    [ 3,  3,  4,  8,  4, 11,  8,  4,  5,  5,  5,  7],  # cons
    [ 2,  3,  4,  8,  0, 11,  6,  8,  9,  5, 11,  7],  # ρ
    [ 3,  4,  0,  3,  2,  0, 11,  2, 11,  2,  2,  0],  # apply
    [ 4,  2,  2,  2,  2,  0, 11,  5, 11,  0,  0,  0],  # cc
    [ 0,  1,  1,  1,  0,  1,  0,  0,  0,  1,  0,  1],  # τ
    [ 4,  2,  6,  0,  0,  2, 11,  6,  8,  6,  2, 11],  # Y
]

CORE_N = 12

# ══════════════════════════════════════════════════════════════════
# Build the full 64×64 table
# ══════════════════════════════════════════════════════════════════

def build_full_table():
    T = [[BOT] * N for _ in range(N)]

    # ── Step 1: Embed the 12×12 core ─────────────────────────────
    for i in range(CORE_N):
        for j in range(CORE_N):
            T[i][j] = CORE_TABLE[i][j]

    # ── Step 2: Absorber rows extend to full width ───────────────
    for j in range(N):
        T[TOP][j] = TOP
        T[BOT][j] = BOT

    # ── Step 3: Fixnum arithmetic block ──────────────────────────
    for a in range(32):
        for b in range(32):
            s = a + b
            if s <= 31:
                T[fixnum(a)][fixnum(b)] = fixnum(s)
            else:
                T[fixnum(a)][fixnum(b)] = BOT  # overflow

    # ── Step 4: Classifier (τ) on all elements ───────────────────
    # Core already set. Extend to the rest.
    # Fixnums → number marker
    for j in range(FIXNUM_BASE, FIXNUM_BASE + FIXNUM_COUNT):
        T[TAU][j] = fixnum(0)  # "number" type marker
    # Type tags → themselves
    for j in [T_PAIR, T_SYM, T_CHAR, T_VEC, T_STR, T_CLS]:
        T[TAU][j] = j
    # Built-in symbols → symbol tag
    for j in range(SYM_LAMBDA, SYM_ELSE + 1):
        T[TAU][j] = T_SYM
    # Specials
    T[TAU][TRUE] = TRUE
    T[TAU][EOF] = EOF
    T[TAU][VOID] = VOID
    T[TAU][TAIL] = TAIL
    T[TAU][RESERVED_0] = BOT
    T[TAU][RESERVED_1] = BOT

    # ── Step 5: Type dispatch for core operators ─────────────────
    # CAR: only valid on pairs
    T[CAR][T_PAIR] = T_PAIR   # valid → runtime resolves
    for j in [T_SYM, T_CHAR, T_VEC, T_STR, T_CLS]:
        T[CAR][j] = BOT
    for j in range(FIXNUM_BASE, FIXNUM_BASE + FIXNUM_COUNT):
        T[CAR][j] = BOT
    for j in range(SYM_LAMBDA, SYM_ELSE + 1):
        T[CAR][j] = BOT
    for j in [TRUE, EOF, VOID, TAIL, RESERVED_0, RESERVED_1]:
        T[CAR][j] = BOT

    # CDR: same dispatch as CAR
    T[CDR][T_PAIR] = T_PAIR
    for j in [T_SYM, T_CHAR, T_VEC, T_STR, T_CLS]:
        T[CDR][j] = BOT
    for j in range(FIXNUM_BASE, FIXNUM_BASE + FIXNUM_COUNT):
        T[CDR][j] = BOT
    for j in range(SYM_LAMBDA, SYM_ELSE + 1):
        T[CDR][j] = BOT
    for j in [TRUE, EOF, VOID, TAIL, RESERVED_0, RESERVED_1]:
        T[CDR][j] = BOT

    # CONS on non-core columns: cons of a type-tagged value
    # cons(pair) → pair (wrapping a pair in another pair is valid)
    T[CONS][T_PAIR] = T_PAIR
    T[CONS][T_SYM] = T_PAIR   # cons of a symbol → makes a pair
    T[CONS][T_CHAR] = T_PAIR
    T[CONS][T_VEC] = T_PAIR
    T[CONS][T_STR] = T_PAIR
    T[CONS][T_CLS] = T_PAIR
    for j in range(FIXNUM_BASE, FIXNUM_BASE + FIXNUM_COUNT):
        T[CONS][j] = T_PAIR   # cons of a fixnum → pair
    for j in range(SYM_LAMBDA, SYM_ELSE + 1):
        T[CONS][j] = T_PAIR
    for j in [TRUE, EOF, VOID, TAIL]:
        T[CONS][j] = T_PAIR
    T[CONS][RESERVED_0] = BOT
    T[CONS][RESERVED_1] = BOT

    # Q/E on non-core: Q encodes, E decodes
    # Q on type tags and fixnums: produce an encoded form
    # For simplicity, Q(fixnum(n)) = fixnum(n) (fixnums are self-quoting)
    for j in range(FIXNUM_BASE, FIXNUM_BASE + FIXNUM_COUNT):
        T[Q][j] = j   # self-quoting
        T[E][j] = j   # self-evaluating
    # Q on type tags: produce encoded form
    for j in [T_PAIR, T_SYM, T_CHAR, T_VEC, T_STR, T_CLS]:
        T[Q][j] = j   # type tags are structural, self-quoting
        T[E][j] = j
    # Q/E on built-in symbols: self-quoting
    for j in range(SYM_LAMBDA, SYM_ELSE + 1):
        T[Q][j] = j
        T[E][j] = j
    # Q/E on specials
    for j in [TRUE, EOF, VOID, TAIL]:
        T[Q][j] = j
        T[E][j] = j
    T[Q][RESERVED_0] = BOT
    T[Q][RESERVED_1] = BOT
    T[E][RESERVED_0] = BOT
    T[E][RESERVED_1] = BOT

    # RHO (branch) on non-core: follow τ dispatch
    # ρ·x = car·x if τ·x is "truthy" (TOP or self), else cons·x
    for j in range(CORE_N, N):
        tau_j = T[TAU][j]
        # Truthy: TOP, TRUE, type tags, fixnum marker
        if tau_j == TOP or tau_j == TRUE:
            T[RHO][j] = T[CAR][j]
        elif tau_j == BOT:
            T[RHO][j] = T[CONS][j]
        else:
            # Type-tagged value: truthy (non-BOT, non-TOP)
            T[RHO][j] = T[CAR][j]

    # ── Step 6: Fixnum rows on non-fixnum columns ────────────────
    # Fixnum applied to non-fixnum: type error (BOT)
    # Already BOT by default. Set a few useful ones:
    for a in range(32):
        # fixnum(a) on absorbers
        T[fixnum(a)][TOP] = TOP   # n · nil = nil (absorber)
        T[fixnum(a)][BOT] = BOT   # n · #f = #f

    # ── Step 7: Type tag rows ────────────────────────────────────
    # Type tags as operators: T_PAIR(x) = "tag x as pair" etc.
    # This is the constructor behavior.
    for j in range(N):
        if j == TOP or j == BOT:
            T[T_PAIR][j] = j  # absorbers absorb
            T[T_SYM][j] = j
            T[T_CHAR][j] = j
            T[T_VEC][j] = j
            T[T_STR][j] = j
            T[T_CLS][j] = j
        else:
            T[T_PAIR][j] = T_PAIR   # tagging
            T[T_SYM][j] = T_SYM
            T[T_CHAR][j] = T_CHAR
            T[T_VEC][j] = T_VEC
            T[T_STR][j] = T_STR
            T[T_CLS][j] = T_CLS

    # ── Step 8: Symbol rows ──────────────────────────────────────
    # Built-in symbols as operators: they evaluate to themselves
    # (symbols are data, not operators in R4RS)
    for sym in range(SYM_LAMBDA, SYM_ELSE + 1):
        T[sym][TOP] = TOP
        T[sym][BOT] = BOT
        # Make each symbol row unique by including the symbol index
        for j in range(2, CORE_N):
            T[sym][j] = sym  # constant function on core (returns self)
        # On fixnums: unique pattern using symbol index
        for j in range(FIXNUM_BASE, FIXNUM_BASE + FIXNUM_COUNT):
            T[sym][j] = fixnum((sym - SYM_LAMBDA + fixnum_val(j)) % 32) \
                        if fixnum_val(j) is not None else BOT

    # ── Step 9: Special value rows ───────────────────────────────
    # #t: truthy absorber-like (maps everything to TRUE except absorbers)
    T[TRUE][TOP] = TOP
    T[TRUE][BOT] = BOT
    for j in range(2, N):
        T[TRUE][j] = TRUE

    # EOF: similar pattern but distinct
    T[EOF][TOP] = TOP
    T[EOF][BOT] = BOT
    for j in range(2, N):
        T[EOF][j] = EOF

    # VOID: similar
    T[VOID][TOP] = TOP
    T[VOID][BOT] = BOT
    for j in range(2, N):
        T[VOID][j] = VOID

    # TAIL: tail-call marker
    T[TAIL][TOP] = TOP
    T[TAIL][BOT] = BOT
    for j in range(2, N):
        T[TAIL][j] = TAIL

    # Reserved: distinct from everything
    T[RESERVED_0][TOP] = TOP
    T[RESERVED_0][BOT] = BOT
    for j in range(2, N):
        T[RESERVED_0][j] = RESERVED_0

    T[RESERVED_1][TOP] = TOP
    T[RESERVED_1][BOT] = TOP  # note: TOP not BOT — makes row unique
    for j in range(2, N):
        T[RESERVED_1][j] = RESERVED_1

    # ── Step 10: Remaining core rows on non-core columns ─────────
    # APPLY, CC, Y, ETA on type tags, fixnums, symbols, specials
    # These need to be filled to make rows unique.
    # Apply on typed values: runtime handles, table just needs to be unique
    for j in range(CORE_N, N):
        T[APPLY][j] = APPLY if j not in (TOP, BOT) else T[APPLY][j]
        T[CC][j] = CC if j not in (TOP, BOT) else T[CC][j]
        T[Y][j] = Y if j not in (TOP, BOT) else T[Y][j]
        T[ETA][j] = ETA if j not in (TOP, BOT) else T[ETA][j]

    # Fix: make APPLY, CC, Y, ETA rows distinguishable from each other
    # by varying their response to the first type tag column
    T[APPLY][T_PAIR] = APPLY
    T[APPLY][T_SYM] = T_CLS   # apply on a symbol → closure dispatch
    T[CC][T_PAIR] = CC
    T[CC][T_SYM] = CC
    T[Y][T_PAIR] = Y
    T[Y][T_SYM] = T_PAIR
    T[ETA][T_PAIR] = ETA
    T[ETA][T_SYM] = ETA

    return T


def verify_extensionality(T):
    """Check all 64 rows are distinct."""
    rows = [tuple(T[i]) for i in range(N)]
    unique_rows = set(rows)
    if len(unique_rows) == N:
        print(f"Extensionality: OK ({N}/{N} unique rows)")
        return True
    else:
        print(f"Extensionality: FAIL ({len(unique_rows)}/{N} unique)")
        # Find collisions
        seen = {}
        for i, row in enumerate(rows):
            if row in seen:
                print(f"  COLLISION: {NAMES[i]} == {NAMES[seen[row]]}")
            else:
                seen[row] = i
        return False


def verify_core_preserved(T):
    """Verify the 12×12 core sub-algebra is preserved."""
    ok = True
    for i in range(CORE_N):
        for j in range(CORE_N):
            if T[i][j] != CORE_TABLE[i][j]:
                print(f"  Core broken at [{NAMES[i]}][{NAMES[j]}]: "
                      f"expected {CORE_TABLE[i][j]}, got {T[i][j]}")
                ok = False
    if ok:
        print("Core sub-algebra: preserved ✓")
    return ok


def verify_fixnum_arith(T):
    """Verify fixnum addition block."""
    correct = 0
    for a in range(32):
        for b in range(32):
            s = a + b
            expected = fixnum(s) if s <= 31 else BOT
            if T[fixnum(a)][fixnum(b)] == expected:
                correct += 1
    ok = correct == 1024
    print(f"Fixnum addition: {correct}/1024 {'✓' if ok else 'FAIL'}")
    return ok


def emit_rust_table(T):
    """Emit the full 64×64 table as a Rust const array."""
    lines = []
    lines.append("pub static CAYLEY: [[u8; 64]; 64] = [")
    for i in range(N):
        row = ', '.join(f"{T[i][j]:2d}" for j in range(N))
        lines.append(f"    [{row}],  // {NAMES[i]}")
    lines.append("];")
    return '\n'.join(lines)


if __name__ == '__main__':
    T = build_full_table()

    print("=== Verification ===")
    verify_core_preserved(T)
    verify_fixnum_arith(T)
    ext_ok = verify_extensionality(T)

    if not ext_ok:
        print("\nFixing extensionality collisions...")
        # Simple fix: for colliding rows, perturb a non-critical cell
        rows = {}
        for i in range(N):
            row = tuple(T[i])
            if row in rows:
                # Find a column we can perturb (non-core, non-fixnum-block)
                other = rows[row]
                # Try changing T[i][RESERVED_0] or T[i][RESERVED_1]
                for target_col in [RESERVED_0, RESERVED_1]:
                    for val in range(N):
                        T[i][target_col] = val
                        new_row = tuple(T[i])
                        if new_row not in rows:
                            rows[new_row] = i
                            print(f"  Fixed {NAMES[i]}: set [{NAMES[i]}][{NAMES[target_col]}] = {val}")
                            break
                    else:
                        continue
                    break
            else:
                rows[row] = i

        verify_extensionality(T)

    print("\n=== Rust output ===")
    rust_code = emit_rust_table(T)
    print(rust_code[:500] + "\n...\n" + rust_code[-200:])

    # Write to file
    with open('src/cayley_64.rs', 'w') as f:
        f.write("// Auto-generated by table_build.py\n")
        f.write("// 64×64 Cayley table for Kamea Scheme\n")
        f.write("// Core sub-algebra verified by Z3. Full table axioms TBD.\n\n")
        f.write(rust_code)
        f.write("\n")
    print(f"\nWritten to src/cayley_64.rs")
