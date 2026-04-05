"""
search.py — Find the right table size for R4RS Scheme with ribs.

Architecture:
  - Val = tagged pointer: fixnum (tag bit set) or rib pointer
  - Rib = (car: Val, cdr: Val, tag: u8) where tag is a table element
  - Cayley table handles type dispatch: table[operator][rib.tag] → result
  - Native compilation (no VM, no interpreter)

The tag byte indexes into the Cayley table. We need enough elements for:
  - Algebraic core: ⊤, ⊥, Q, E, car, cdr, cons, ρ, τ, Y (10 elements)
  - R4RS type tags: pair, symbol, closure, string, vector, char,
    continuation, port (8 type tags)
  - Special values: #t, eof, void (3 specials)

That's 21 elements minimum. 16 is too tight. 32 gives us room.

Strategy:
  1. Search for a core sub-algebra at N=16 (the proven Ψ₁₆ structure)
  2. If that's too tight for R4RS type tags, expand to N=32
  3. R4RS type tags live outside the core but interact via table dispatch
"""

from z3 import *
import sys

# ══════════════════════════════════════════════════════════════════
# Element layout for N=32
# ══════════════════════════════════════════════════════════════════

# Algebraic core (0-11) — same as the verified search
TOP   = 0    # ⊤, nil
BOT   = 1    # ⊥, #f
Q     = 2    # quote / encoder
E_EL  = 3    # eval / decoder (E_EL to avoid shadowing z3's E)
CAR   = 4    # first projection (f)
CDR   = 5    # second projection / composite (η)
CONS  = 6    # pair constructor / core-preserving (g)
RHO   = 7    # branch (ρ)
APPLY = 8    # explicit apply
CC    = 9    # call/cc
TAU   = 10   # classifier (τ)
Y     = 11   # Y combinator

# R4RS type tags (12-19)
T_PAIR = 12  # pair
T_SYM  = 13  # symbol
T_CLS  = 14  # closure / procedure
T_STR  = 15  # string
T_VEC  = 16  # vector
T_CHAR = 17  # character
T_CONT = 18  # continuation (first-class, for call/cc)
T_PORT = 19  # port (input/output)

# Special values (20-22)
TRUE   = 20  # #t
EOFV   = 21  # eof-object
VOID   = 22  # void

# Available (23-31) — room for growth
# Could add: bytevector, rational, bignum, syntax, etc.

N = 32
CORE = list(range(2, 12))   # non-absorber core elements
TYPE_TAGS = list(range(12, 20))
SPECIALS = [TRUE, EOFV, VOID]

NAMES = [
    '⊤', '⊥', 'Q', 'E', 'car', 'cdr', 'cons', 'ρ',
    'apply', 'cc', 'τ', 'Y',
    'pair', 'sym', 'cls', 'str', 'vec', 'char', 'cont', 'port',
    '#t', 'eof', 'void',
] + [f'_{i}' for i in range(23, 32)]


def search_table():
    """Search for a 32×32 Cayley table satisfying R4RS axioms."""
    s = Solver()
    # Timeout: 60 seconds
    s.set("timeout", 60000)

    T = [[Int(f"T_{i}_{j}") for j in range(N)] for i in range(N)]

    # All values in range
    for i in range(N):
        for j in range(N):
            s.add(T[i][j] >= 0, T[i][j] < N)

    # ── Absorbers ─────────────────────────────────────────────────
    for j in range(N):
        s.add(T[TOP][j] == TOP)
        s.add(T[BOT][j] == BOT)

    # ── E-transparency ────────────────────────────────────────────
    s.add(T[E_EL][TOP] == TOP)
    s.add(T[E_EL][BOT] == BOT)

    # ── Q/E retraction on core ────────────────────────────────────
    for x in CORE:
        s.add(T[Q][x] >= 2, T[Q][x] < 12)  # Q maps core to core
        s.add(T[E_EL][x] >= 2, T[E_EL][x] < 12)
        for y in CORE:
            s.add(Implies(T[Q][x] == y, T[E_EL][y] == x))
            s.add(Implies(T[E_EL][x] == y, T[Q][y] == x))
    for x1 in CORE:
        for x2 in CORE:
            if x1 < x2:
                s.add(T[Q][x1] != T[Q][x2])

    # ── Classifier (τ) on core ────────────────────────────────────
    for x in CORE:
        s.add(Or(T[TAU][x] == TOP, T[TAU][x] == BOT))
    s.add(T[TAU][TOP] == TOP)
    s.add(T[TAU][BOT] == BOT)
    s.add(Sum([If(T[TAU][x] == TOP, 1, 0) for x in CORE]) >= 2)
    s.add(Sum([If(T[TAU][x] == BOT, 1, 0) for x in CORE]) >= 2)

    # ── Classifier on type tags → returns the tag itself ──────────
    for t in TYPE_TAGS:
        s.add(T[TAU][t] == t)
    # Classifier on specials
    s.add(T[TAU][TRUE] == TRUE)
    s.add(T[TAU][EOFV] == EOFV)
    s.add(T[TAU][VOID] == VOID)

    # ── Branch (ρ) on core ────────────────────────────────────────
    for x in CORE:
        s.add(If(T[TAU][x] == TOP,
                 T[RHO][x] == T[CAR][x],
                 T[RHO][x] == T[CONS][x]))
    s.add(T[RHO][TOP] == T[CAR][TOP])
    s.add(T[RHO][BOT] == T[CONS][BOT])

    # ── Composition (cdr = ρ ∘ cons) on core ──────────────────────
    for x in CORE:
        for v in range(N):
            s.add(Implies(T[CONS][x] == v, T[CDR][x] == T[RHO][v]))

    # ── CONS is core-preserving ───────────────────────────────────
    for x in CORE:
        s.add(T[CONS][x] >= 2, T[CONS][x] < 12)

    # ── Y combinator ─────────────────────────────────────────────
    for v in range(N):
        s.add(Implies(T[Y][RHO] == v, T[RHO][v] == v))
    s.add(T[Y][RHO] >= 2)

    # ── Type dispatch: car/cdr on type tags ───────────────────────
    # car of pair → valid (returns T_PAIR as signal to runtime)
    s.add(T[CAR][T_PAIR] == T_PAIR)
    s.add(T[CDR][T_PAIR] == T_PAIR)
    # car/cdr of non-pair types → BOT (error)
    for t in TYPE_TAGS:
        if t != T_PAIR:
            s.add(T[CAR][t] == BOT)
            s.add(T[CDR][t] == BOT)
    # car/cdr on specials → BOT
    for t in SPECIALS:
        s.add(T[CAR][t] == BOT)
        s.add(T[CDR][t] == BOT)

    # ── Type tags as constructors ─────────────────────────────────
    # Applying a type tag to any non-absorber returns the tag (tagging)
    # Applying to absorbers: absorb
    for t in TYPE_TAGS:
        s.add(T[t][TOP] == TOP)
        s.add(T[t][BOT] == BOT)
        for j in range(2, N):
            s.add(T[t][j] == t)

    # ── Special value rows ────────────────────────────────────────
    # #t: truthy (maps non-absorbers to TRUE)
    s.add(T[TRUE][TOP] == TOP)
    s.add(T[TRUE][BOT] == BOT)
    for j in range(2, N):
        s.add(T[TRUE][j] == TRUE)

    # eof, void: similar constant-function behavior but distinct
    s.add(T[EOFV][TOP] == TOP)
    s.add(T[EOFV][BOT] == BOT)
    for j in range(2, N):
        s.add(T[EOFV][j] == EOFV)

    s.add(T[VOID][TOP] == TOP)
    s.add(T[VOID][BOT] == BOT)
    for j in range(2, N):
        s.add(T[VOID][j] == VOID)

    # ── Unused rows (23-31): make distinct ────────────────────────
    # Each unused row is a constant function returning its own index
    # (like the type tags and specials, but with a twist for uniqueness)
    for i in range(23, N):
        s.add(T[i][TOP] == TOP)
        s.add(T[i][BOT] == i)  # differs from type tags (which have BOT)
        for j in range(2, N):
            s.add(T[i][j] == i)

    # ── Extensionality ────────────────────────────────────────────
    # All 32 rows must be distinct
    for i1 in range(N):
        for i2 in range(i1 + 1, N):
            s.add(Or(*[T[i1][j] != T[i2][j] for j in range(N)]))

    # ── Solve ─────────────────────────────────────────────────────
    print(f"Searching for {N}×{N} table...")
    result = s.check()

    if result == sat:
        m = s.model()
        table = [[m.evaluate(T[i][j]).as_long() for j in range(N)]
                 for i in range(N)]
        return table
    else:
        print(f"Result: {result}")
        return None


def verify(T):
    """Verify all axioms."""
    ok = True
    def check(name, cond):
        nonlocal ok
        if not cond:
            print(f"  FAIL: {name}")
            ok = False

    # Absorbers
    for j in range(N):
        check(f"⊤·{j}", T[TOP][j] == TOP)
        check(f"⊥·{j}", T[BOT][j] == BOT)

    # E-transparency
    check("E(⊤)=⊤", T[E_EL][TOP] == TOP)
    check("E(⊥)=⊥", T[E_EL][BOT] == BOT)

    # Retraction
    for x in CORE:
        qx = T[Q][x]
        check(f"E(Q({NAMES[x]}))={NAMES[x]}", T[E_EL][qx] == x)
        ex = T[E_EL][x]
        check(f"Q(E({NAMES[x]}))={NAMES[x]}", T[Q][ex] == x)

    # Classifier on core
    for x in CORE:
        check(f"τ({NAMES[x]})∈{{⊤,⊥}}", T[TAU][x] in (TOP, BOT))
    tops = sum(1 for x in CORE if T[TAU][x] == TOP)
    bots = sum(1 for x in CORE if T[TAU][x] == BOT)
    check(f"τ=⊤ ≥2 ({tops})", tops >= 2)
    check(f"τ=⊥ ≥2 ({bots})", bots >= 2)

    # Classifier on type tags
    for t in TYPE_TAGS:
        check(f"τ({NAMES[t]})={NAMES[t]}", T[TAU][t] == t)

    # Branch
    for x in CORE:
        if T[TAU][x] == TOP:
            check(f"ρ({NAMES[x]})=car({NAMES[x]})", T[RHO][x] == T[CAR][x])
        else:
            check(f"ρ({NAMES[x]})=cons({NAMES[x]})", T[RHO][x] == T[CONS][x])

    # Composition
    for x in CORE:
        gx = T[CONS][x]
        check(f"cdr({NAMES[x]})=ρ(cons({NAMES[x]}))", T[CDR][x] == T[RHO][gx])

    # Core-preserving
    for x in CORE:
        check(f"cons({NAMES[x]})∈core", 2 <= T[CONS][x] < 12)

    # Y fixed point
    yp = T[Y][RHO]
    check(f"Y(ρ) non-absorber", yp >= 2)
    check(f"ρ(Y(ρ))=Y(ρ)", T[RHO][yp] == yp)

    # Type dispatch
    check("car(pair)=pair", T[CAR][T_PAIR] == T_PAIR)
    check("cdr(pair)=pair", T[CDR][T_PAIR] == T_PAIR)
    for t in TYPE_TAGS:
        if t != T_PAIR:
            check(f"car({NAMES[t]})=⊥", T[CAR][t] == BOT)

    # Extensionality
    rows = [tuple(T[i]) for i in range(N)]
    unique = len(set(rows))
    check(f"extensionality ({unique}/{N})", unique == N)

    if ok:
        print("  ALL AXIOMS VERIFIED ✓")
    return ok


def print_table(T):
    """Pretty-print the table."""
    # Print header
    print(f"\n{'':>7s}", end='')
    for j in range(N):
        print(f"{NAMES[j]:>5s}", end='')
    print()
    print("       " + "─" * (5 * N))
    for i in range(N):
        print(f"{NAMES[i]:>6s}│", end='')
        for j in range(N):
            print(f"{NAMES[T[i][j]]:>5s}", end='')
        print()

    # Classifier partition
    print(f"\nClassifier partition (core):")
    t_top = [NAMES[x] for x in CORE if T[TAU][x] == TOP]
    t_bot = [NAMES[x] for x in CORE if T[TAU][x] == BOT]
    print(f"  τ=⊤: {', '.join(t_top)}")
    print(f"  τ=⊥: {', '.join(t_bot)}")


def emit_rust(T):
    """Emit as Rust const array."""
    lines = []
    lines.append(f"// Auto-generated by search.py (v2)")
    lines.append(f"// {N}×{N} Cayley table for Kamea Scheme")
    lines.append(f"// Core sub-algebra verified by Z3")
    lines.append(f"")
    lines.append(f"pub static CAYLEY: [[u8; {N}]; {N}] = [")
    for i in range(N):
        row = ', '.join(f"{T[i][j]:2d}" for j in range(N))
        lines.append(f"    [{row}],  // {NAMES[i]}")
    lines.append("];")
    return '\n'.join(lines)


if __name__ == '__main__':
    T = search_table()
    if T is None:
        print("No solution found.")
        sys.exit(1)

    print("\nFound valid table!")
    print_table(T)
    print("\nVerification:")
    if verify(T):
        rust = emit_rust(T)
        outpath = 'v2/src/cayley_32.rs'
        with open(outpath, 'w') as f:
            f.write(rust + '\n')
        print(f"\nWritten to {outpath}")
        print(f"Table size: {N*N} bytes = {N*N/1024:.1f} KB")
