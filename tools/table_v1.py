"""
table.py — 64×64 Cayley table generator for Kamea Scheme.

Generates the 4KB table that implements:
  - Algebraic core (retraction pair, classifier, composition)
  - Type-dispatched operations (car/cdr/cons on typed values)
  - Immediate fixnum arithmetic (0-31)
  - Type predicates via classifier

The table is the runtime. Everything else is scaffolding.
"""

# ═══════════════════════════════════════════════════════════════════
# Element indices
# ═══════════════════════════════════════════════════════════════════

# Algebraic core
TOP   = 0   # ⊤, nil, empty list
BOT   = 1   # ⊥, #f, error
Q     = 2   # quote / encoder
E     = 3   # eval / decoder
CAR   = 4   # first projection
CDR   = 5   # second projection
CONS  = 6   # pair constructor

# Control
RHO   = 7   # branch / conditional
APPLY = 8   # explicit apply
CC    = 9   # call/cc marker

# Classifier and Y combinator
TAU   = 10  # classifier / type predicate
Y     = 11  # Y combinator (fixed point)
ETA   = Y   # alias — CDR (5) is the composite element, not ETA

# Type tags
T_PAIR = 12
T_SYM  = 13
T_CHAR = 14
T_VEC  = 15
T_STR  = 16
T_CLS  = 17

# Immediate fixnums: 18..49 represent integers 0..31
FIXNUM_BASE = 18
FIXNUM_COUNT = 32

def fixnum(n):
    """Element index for immediate fixnum n (0 <= n <= 31)."""
    assert 0 <= n <= 31, f"fixnum out of range: {n}"
    return FIXNUM_BASE + n

def fixnum_val(elem):
    """Integer value of a fixnum element, or None if not a fixnum."""
    if FIXNUM_BASE <= elem < FIXNUM_BASE + FIXNUM_COUNT:
        return elem - FIXNUM_BASE
    return None

# Built-in symbols
SYM_LAMBDA = 50
SYM_IF     = 51
SYM_DEFINE = 52
SYM_QUOTE  = 53
SYM_SET    = 54
SYM_BEGIN  = 55
SYM_COND   = 56
SYM_ELSE   = 57

# Special values
TRUE  = 58  # #t
EOF   = 59  # eof-object
VOID  = 60  # void / unspecified
TAIL  = 61  # tail-call marker

# Reserved
RESERVED_0 = 62
RESERVED_1 = 63

N = 64  # table size

# Element names for display
NAMES = ['⊤', '⊥', 'Q', 'E', 'car', 'cdr', 'cons',
         'ρ', 'apply', 'cc',
         'τ', 'Y',
         'T_pair', 'T_sym', 'T_char', 'T_vec', 'T_str', 'T_cls'] + \
        [str(i) for i in range(32)] + \
        ['λ', 'if', 'define', 'quote', 'set!', 'begin', 'cond', 'else'] + \
        ['#t', 'eof', 'void', 'tail', '_62', '_63']


# ═══════════════════════════════════════════════════════════════════
# Table construction
# ═══════════════════════════════════════════════════════════════════

def make_table():
    """Build the 64×64 Cayley table."""
    T = [[BOT] * N for _ in range(N)]

    # --- Absorber rows ---
    # ⊤ · x = ⊤ for all x  (top absorber = nil)
    for j in range(N):
        T[TOP][j] = TOP
    # ⊥ · x = ⊥ for all x  (bottom absorber = #f)
    for j in range(N):
        T[BOT][j] = BOT

    # --- Retraction pair (Q/E) ---
    # E(Q(x)) = x for all non-absorber x
    # Q(E(x)) = x for all non-absorber x
    # Q(⊤) = some fixed encoding, Q(⊥) = some fixed encoding
    # E(⊤) = ⊤ (E-transparency), E(⊥) = ⊥ (E-transparency)
    for j in range(N):
        if j == TOP:
            T[E][j] = TOP   # E-transparency
            T[Q][j] = fixnum(0)  # Q(⊤) = encoding of ⊤
        elif j == BOT:
            T[E][j] = BOT   # E-transparency
            T[Q][j] = fixnum(1)  # Q(⊥) = encoding of ⊥
        else:
            # For core elements, Q encodes and E decodes
            # Full specification TBD during table search
            pass

    # --- Classifier (τ) ---
    # τ(x) returns the type tag of x
    T[TAU][TOP] = TOP        # τ(nil) = nil (it's nil)
    T[TAU][BOT] = BOT        # τ(#f) = #f
    T[TAU][TRUE] = TRUE      # τ(#t) = #t (boolean)
    # Type tags for typed values
    for j in range(FIXNUM_BASE, FIXNUM_BASE + FIXNUM_COUNT):
        T[TAU][j] = fixnum(0)  # τ(fixnum) = "number" marker
    # τ(type-tag) = type-tag (type tags classify themselves)
    for j in [T_PAIR, T_SYM, T_CHAR, T_VEC, T_STR, T_CLS]:
        T[TAU][j] = j

    # --- Fixnum arithmetic ---
    # This is the big payoff: add(a, b) as table lookup for small values.
    # We define element-level addition for the fixnum block.
    # T[fixnum(a)][fixnum(b)] = fixnum(a+b) if a+b <= 31, else overflow marker
    for a in range(32):
        for b in range(32):
            s = a + b
            if s <= 31:
                T[fixnum(a)][fixnum(b)] = fixnum(s)
            else:
                T[fixnum(a)][fixnum(b)] = BOT  # overflow → runtime handles it

    # --- Type dispatch for car/cdr ---
    # car applied to a type tag determines behavior
    # (actual pair car/cdr goes through heap; the table handles type checking)
    T[CAR][T_PAIR] = T_PAIR   # car of a pair → valid (runtime resolves)
    T[CAR][T_SYM]  = BOT      # car of a symbol → error
    T[CAR][T_CHAR] = BOT      # car of a char → error
    T[CAR][T_VEC]  = BOT      # car of a vector → error
    T[CAR][T_STR]  = BOT      # car of a string → error
    T[CAR][T_CLS]  = BOT      # car of a closure → error
    for j in range(FIXNUM_BASE, FIXNUM_BASE + FIXNUM_COUNT):
        T[CAR][j] = BOT       # car of a number → error

    T[CDR][T_PAIR] = T_PAIR   # cdr of a pair → valid
    T[CDR][T_SYM]  = BOT
    T[CDR][T_CHAR] = BOT
    T[CDR][T_VEC]  = BOT
    T[CDR][T_STR]  = BOT
    T[CDR][T_CLS]  = BOT
    for j in range(FIXNUM_BASE, FIXNUM_BASE + FIXNUM_COUNT):
        T[CDR][j] = BOT

    # TODO: Fill remaining rows to satisfy:
    #   - Extensionality (all rows distinct)
    #   - ICP (internal composition property)
    #   - Branch semantics
    #   - Composition (η)
    #   - Y combinator (if included)
    #   - Full type dispatch for all operators × all types

    return T


def print_table(T):
    """Print the table in a readable format."""
    print(f"{'':>6s}", end='')
    for j in range(N):
        print(f"{NAMES[j]:>5s}", end='')
    print()
    for i in range(N):
        print(f"{NAMES[i]:>6s}", end='')
        for j in range(N):
            print(f"{NAMES[T[i][j]]:>5s}", end='')
        print()


def emit_c_table(T):
    """Emit the table as a C const array."""
    print("static const uint8_t cayley[64][64] = {")
    for i in range(N):
        row = ', '.join(f"{T[i][j]:2d}" for j in range(N))
        print(f"    {{{row}}},  /* {NAMES[i]} */")
    print("};")


def emit_stats(T):
    """Print table statistics."""
    # Check extensionality
    rows = [tuple(T[i]) for i in range(N)]
    unique = len(set(rows))
    print(f"Rows: {N}, Unique: {unique}, "
          f"{'EXTENSIONAL' if unique == N else f'COLLISIONS: {N - unique}'}")

    # Check absorbers
    top_ok = all(T[TOP][j] == TOP for j in range(N))
    bot_ok = all(T[BOT][j] == BOT for j in range(N))
    print(f"⊤ absorber: {'OK' if top_ok else 'FAIL'}")
    print(f"⊥ absorber: {'OK' if bot_ok else 'FAIL'}")

    # Fixnum arithmetic check
    correct = 0
    total = 0
    for a in range(32):
        for b in range(32):
            total += 1
            s = a + b
            if s <= 31:
                if T[fixnum(a)][fixnum(b)] == fixnum(s):
                    correct += 1
            else:
                if T[fixnum(a)][fixnum(b)] == BOT:
                    correct += 1
    print(f"Fixnum addition: {correct}/{total} correct")


if __name__ == '__main__':
    T = make_table()
    emit_stats(T)
    print()
    print("C table output:")
    emit_c_table(T)
