"""
table_search.py — Z3 search for the 12×12 core sub-algebra.

Finds a valid assignment for the core elements (0-11) satisfying:
  - Absorbers (⊤=0, ⊥=1)
  - Extensionality (all 12 rows distinct)
  - Q/E retraction on core {2..11}
  - E-transparency (E(⊤)=⊤, E(⊥)=⊥)
  - Classifier τ maps core to {⊤, ⊥} with both values hit
  - Branch: ρ·x = car·x if τ·x = ⊤, else ρ·x = cons·x
  - Compose: cdr·x = ρ·(cons·x)

Once the 12×12 core is found, it's embedded into the full 64×64 table.
"""

from z3 import *

# Element indices (same as table.py)
TOP  = 0
BOT  = 1
Q    = 2
E    = 3
CAR  = 4   # f in Ψ₁₆
CDR  = 5   # η in Ψ₁₆ (composite)
CONS = 6   # g in Ψ₁₆ (core-preserving)
RHO  = 7   # ρ in Ψ₁₆ (branch)
APPLY = 8
CC   = 9
TAU  = 10  # τ in Ψ₁₆ (classifier)
Y    = 11  # Y combinator

N = 12  # core sub-algebra size
CORE = list(range(2, N))  # non-absorber elements

NAMES = ['⊤', '⊥', 'Q', 'E', 'car', 'cdr', 'cons', 'ρ', 'apply', 'cc', 'τ', 'Y']

def search_core():
    s = Solver()

    # T[i][j] = result of applying element i to element j
    T = [[Int(f"T_{i}_{j}") for j in range(N)] for i in range(N)]

    # All values in range [0, N)
    for i in range(N):
        for j in range(N):
            s.add(T[i][j] >= 0, T[i][j] < N)

    # ── Absorbers ─────────────────────────────────────────────────
    for j in range(N):
        s.add(T[TOP][j] == TOP)
        s.add(T[BOT][j] == BOT)

    # ── E-transparency ────────────────────────────────────────────
    s.add(T[E][TOP] == TOP)
    s.add(T[E][BOT] == BOT)

    # ── Q/E retraction on core ────────────────────────────────────
    # Q and E are inverse permutations on core {2..11}
    for x in CORE:
        # Q(x) must be in core (can't map to absorber since E inverts
        # and E(TOP)=TOP, E(BOT)=BOT)
        s.add(T[Q][x] >= 2)
        s.add(T[E][x] >= 2)
        # Round-trip
        for y in CORE:
            # If Q(x) = y, then E(y) = x
            s.add(Implies(T[Q][x] == y, T[E][y] == x))
            # If E(x) = y, then Q(y) = x
            s.add(Implies(T[E][x] == y, T[Q][y] == x))

    # Q is injective on core (redundant with retraction but helps solver)
    for x1 in CORE:
        for x2 in CORE:
            if x1 < x2:
                s.add(T[Q][x1] != T[Q][x2])

    # ── Classifier (τ) ───────────────────────────────────────────
    # τ maps core to {TOP, BOT} (boolean outputs)
    for x in CORE:
        s.add(Or(T[TAU][x] == TOP, T[TAU][x] == BOT))

    # τ on absorbers
    s.add(T[TAU][TOP] == TOP)
    s.add(T[TAU][BOT] == BOT)

    # At least one core element classified as TOP (tester-like)
    s.add(Or(*[T[TAU][x] == TOP for x in CORE]))
    # At least one core element classified as BOT
    s.add(Or(*[T[TAU][x] == BOT for x in CORE]))

    # τ is not itself boolean-valued on everything — it should classify
    # at least 2 elements each way for non-degeneracy
    s.add(Sum([If(T[TAU][x] == TOP, 1, 0) for x in CORE]) >= 2)
    s.add(Sum([If(T[TAU][x] == BOT, 1, 0) for x in CORE]) >= 2)

    # ── Branch (ρ) ────────────────────────────────────────────────
    # ρ·x = car·x if τ·x = ⊤, else ρ·x = cons·x
    for x in CORE:
        s.add(If(T[TAU][x] == TOP,
                 T[RHO][x] == T[CAR][x],
                 T[RHO][x] == T[CONS][x]))

    # ρ on absorbers: follow the rule
    s.add(T[RHO][TOP] == T[CAR][TOP])   # τ(⊤)=⊤, so ρ(⊤)=car(⊤)
    s.add(T[RHO][BOT] == T[CONS][BOT])  # τ(⊥)=⊥, so ρ(⊥)=cons(⊥)

    # ── Composition (cdr = ρ ∘ cons) ─────────────────────────────
    # cdr·x = ρ·(cons·x) for all x in core
    for x in CORE:
        # We need to express: T[CDR][x] = T[RHO][T[CONS][x]]
        # Since T[CONS][x] is a variable, we case-split
        for v in range(N):
            s.add(Implies(T[CONS][x] == v, T[CDR][x] == T[RHO][v]))

    # ── CONS is core-preserving ───────────────────────────────────
    # cons maps core to core (needed for ICP)
    for x in CORE:
        s.add(T[CONS][x] >= 2)

    # ── Y combinator ─────────────────────────────────────────────
    # Y·ρ = ρ·(Y·ρ) — fixed-point property
    # Y·ρ must be a non-absorber
    for v in range(N):
        s.add(Implies(T[Y][RHO] == v, T[RHO][v] == v))
    s.add(T[Y][RHO] >= 2)  # non-absorber

    # ── Extensionality ────────────────────────────────────────────
    # All 12 rows must be distinct
    for i1 in range(N):
        for i2 in range(i1 + 1, N):
            # At least one column differs
            s.add(Or(*[T[i1][j] != T[i2][j] for j in range(N)]))

    # ── Solve ─────────────────────────────────────────────────────
    print("Searching for 12×12 core sub-algebra...")
    result = s.check()

    if result == sat:
        m = s.model()
        table = [[m.evaluate(T[i][j]).as_long() for j in range(N)]
                 for i in range(N)]
        return table
    else:
        print(f"Result: {result}")
        return None


def verify_core(T):
    """Verify all axioms on the found table."""
    ok = True

    def check(name, cond):
        nonlocal ok
        if not cond:
            print(f"  FAIL: {name}")
            ok = False

    # Absorbers
    for j in range(N):
        check(f"⊤·{j}=⊤", T[TOP][j] == TOP)
        check(f"⊥·{j}=⊥", T[BOT][j] == BOT)

    # E-transparency
    check("E(⊤)=⊤", T[E][TOP] == TOP)
    check("E(⊥)=⊥", T[E][BOT] == BOT)

    # Retraction
    for x in CORE:
        qx = T[Q][x]
        check(f"E(Q({NAMES[x]}))={NAMES[x]}", T[E][qx] == x)
        ex = T[E][x]
        check(f"Q(E({NAMES[x]}))={NAMES[x]}", T[Q][ex] == x)

    # Classifier
    for x in CORE:
        check(f"τ({NAMES[x]})∈{{⊤,⊥}}", T[TAU][x] in (TOP, BOT))

    tops = sum(1 for x in CORE if T[TAU][x] == TOP)
    bots = sum(1 for x in CORE if T[TAU][x] == BOT)
    check(f"τ hits ⊤ ≥2 (got {tops})", tops >= 2)
    check(f"τ hits ⊥ ≥2 (got {bots})", bots >= 2)

    # Branch
    for x in CORE:
        if T[TAU][x] == TOP:
            check(f"ρ({NAMES[x]})=car({NAMES[x]})",
                  T[RHO][x] == T[CAR][x])
        else:
            check(f"ρ({NAMES[x]})=cons({NAMES[x]})",
                  T[RHO][x] == T[CONS][x])

    # Composition
    for x in CORE:
        gx = T[CONS][x]
        check(f"cdr({NAMES[x]})=ρ(cons({NAMES[x]}))",
              T[CDR][x] == T[RHO][gx])

    # Core-preserving
    for x in CORE:
        check(f"cons({NAMES[x]})∈core", T[CONS][x] >= 2)

    # Y fixed point
    yp = T[Y][RHO]
    check(f"Y(ρ)={NAMES[yp]}, ρ(Y(ρ))=Y(ρ)", T[RHO][yp] == yp)
    check("Y(ρ) non-absorber", yp >= 2)

    # Extensionality
    rows = [tuple(T[i]) for i in range(N)]
    unique = len(set(rows))
    check(f"extensionality ({unique}/{N} unique)", unique == N)

    if ok:
        print("  ALL AXIOMS VERIFIED ✓")
    return ok


def print_core(T):
    """Pretty-print the 12×12 core table."""
    print(f"\n{'':>7s}", end='')
    for j in range(N):
        print(f"{NAMES[j]:>6s}", end='')
    print()
    print("       " + "─" * (6 * N))
    for i in range(N):
        print(f"{NAMES[i]:>6s}│", end='')
        for j in range(N):
            v = T[i][j]
            print(f"{NAMES[v]:>6s}", end='')
        print()

    # Show classifier partition
    print(f"\nClassifier partition:")
    tops = [NAMES[x] for x in CORE if T[TAU][x] == TOP]
    bots = [NAMES[x] for x in CORE if T[TAU][x] == BOT]
    print(f"  τ=⊤ (true):  {', '.join(tops)}")
    print(f"  τ=⊥ (false): {', '.join(bots)}")

    # Show Q permutation
    print(f"\nQ permutation on core:")
    for x in CORE:
        print(f"  Q({NAMES[x]}) = {NAMES[T[Q][x]]}", end='')
    print()

    # Show composition
    print(f"\nComposition check (cdr = ρ ∘ cons):")
    for x in CORE:
        gx = T[CONS][x]
        print(f"  cdr({NAMES[x]}) = {NAMES[T[CDR][x]]}, "
              f"ρ(cons({NAMES[x]})) = ρ({NAMES[gx]}) = {NAMES[T[RHO][gx]]}")


def emit_rust_core(T):
    """Emit the 12×12 sub-table as Rust array literal."""
    print("\n// 12×12 core sub-algebra (to embed in the 64×64 table)")
    print("const CORE: [[u8; 12]; 12] = [")
    for i in range(N):
        row = ', '.join(f"{T[i][j]:2d}" for j in range(N))
        print(f"    [{row}],  // {NAMES[i]}")
    print("];")


if __name__ == '__main__':
    T = search_core()
    if T is not None:
        print("\nFound valid core sub-algebra!")
        print_core(T)
        print("\nVerification:")
        verify_core(T)
        emit_rust_core(T)
    else:
        print("No solution found.")
