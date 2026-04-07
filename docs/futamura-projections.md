# Futamura Projections in WispyScheme

How a 1KB Cayley table, a partial evaluator, and a CPS meta-evaluator combine to eliminate interpretation overhead while preserving call/cc.

## Background

The Futamura projections (1971, 1999) show that a partial evaluator applied to an interpreter produces increasingly powerful artifacts:

```
P1: specialize(interpreter, program)     = compiled program
P2: specialize(specializer, interpreter) = compiler
P3: specialize(specializer, specializer) = compiler-compiler
```

WispyScheme demonstrates all three projections on a toy algebra interpreter, P1 on a real Scheme evaluator, and P2 on a CPS evaluator with inspectable continuations.

## What WispyScheme Has

### The Online Partial Evaluator (`examples/pe.scm`)

An online PE for Scheme, written in Scheme, running on WispyScheme. It operates on quoted S-expressions with a function table and depth-limited unfolding.

The PE distinguishes three kinds of values:
- **Known** — concrete values that can be folded at specialization time
- **Unknown** — runtime values represented by `(make-unknown 'name)`, with the name preserved for readable residual code
- **Residual** — code that must remain in the output, wrapped with `(make-residual expr)`

When all arguments to an operation are known, the PE folds it to a value. When some are unknown, it produces residual code. When a function body evaluates to generic unknown, the PE residualizes the function call itself.

Handles: arithmetic, comparison, `if`, `cond`, `let`, `begin`, `car`/`cdr`/`cons`, `list`, type predicates, `eq?`/`equal?`, boolean connectives, and depth-limited function unfolding.

### The CPS Meta-Evaluator (`examples/metacircular.scm`)

A defunctionalized CPS Scheme interpreter with 14 continuation types, all represented as tagged lists — inspectable, serializable, and modifiable at runtime. Follows Smith's 3-Lisp (1984), Reynolds' definitional interpreters (1972), and Danvy & Nielsen's defunctionalization (2001).

Core architecture:
- `meval expr env k` — evaluates an expression in CPS
- `apply-k k val` — dispatches on continuation tag (14 types)
- `mapply fn args k` — applies closure or builtin
- `eval-args`, `eval-cond`, `eval-let-bindings`, `eval-sequence` — CPS helpers

The key feature: continuations are data, not closures. A continuation like `(list 'k-if then-branch else-branch env k)` can be walked, inspected, modified, and reflected into. This is what makes `reify`/`reflect` and continuation surgery possible.

## Projection 1: Interpreter Elimination

**File:** `examples/futamura-real.scm`

A 40-line direct-style evaluator (`deval`) handles numbers, booleans, symbols, `if`, arithmetic (`+`, `-`, `*`, `<`, `=`), and single-argument recursive function calls. We register it in the PE and specialize with a known program.

```scheme
(pe-specialize 'deval '(fib 8) '() fib-fns)  ;; → 21
```

The PE unfolds every `cond` dispatch in `deval`, every `car`/`cdr` traversal of the program structure, every symbol lookup — the interpreter vanishes. What remains is the bare computation: `21`.

**Four-path verification:** direct Scheme, `deval` interpretation, and PE specialization all produce `21`.

## Projection 2: CPS Compiler

**File:** `examples/futamura-cps.scm`

This is the main result. We register all 16 functions of the CPS evaluator in the PE's function table:

- Core: `meval`, `apply-k`, `mapply`
- Helpers: `eval-args`, `eval-cond`, `eval-let-bindings`, `eval-sequence`
- Environment: `m-nth`, `m-assoc`, `m-lookup`, `extend-env`
- Values: `make-closure`, `closure?`, `builtin?`, `apply-builtin`

Then `cps-compile` wraps `pe-specialize`:

```scheme
(define (cps-compile program)
  (pe-specialize 'meval program base-menv (make-unknown 'k)))
```

The program and environment are **known**. The continuation `k` is **unknown** (it's a runtime value — we don't know who's calling us). The PE specializes `meval` with respect to the known program structure while leaving continuation operations as residual code.

### Fully-Known Programs

When all inputs are known, the entire CPS evaluator folds away:

```
42                          → (apply-k k 42)
(+ 1 2)                    → (apply-k k 3)
(+ (* 3 4) (- 10 5))       → (apply-k k 17)
(if #t 1 2)                → (apply-k k 1)
(let ((x 5)) (+ x 1))      → (apply-k k 6)
((lambda (x) (+ x 1)) 5)   → (apply-k k 6)
```

For `(+ 1 2)`, the PE:
1. Folds `(pair? '(+ 1 2))` → `#t`
2. Folds `(car '(+ 1 2))` → `+`
3. Folds `(eq? '+ 'quote)` → `#f`, `(eq? '+ 'if)` → `#f`, ... falls through to function application
4. Folds `(m-lookup '+ base-menv)` → `(91 +)` (the builtin)
5. Folds `(builtin? (91 +))` → `#t`
6. Unfolds `eval-args`, evaluates `1` and `2` through `meval`
7. Folds `(apply-builtin '+ '(1 2))` → `3`
8. Reaches `(apply-k k 3)` — k is unknown, so residualizes the call

All of `meval`'s expression type dispatch, `apply-k`'s continuation tag dispatch, `m-lookup`'s alist traversal, and `apply-builtin`'s name matching — eliminated.

### Partially-Known Programs

When the program has free variables, the PE folds the interpreter dispatch but leaves runtime computation as residual code:

```
x                           → (apply-k k x)
(+ x 1)                    → (apply-k k (+ a1 a2))
(if (< x 0) (- 0 x) x)    → (if val (apply-k k (- a1 a2)) (apply-k k x))
(if #t x y)                → (apply-k k x)       ;; dead branch y eliminated!
(+ (* 2 3) x)              → (apply-k k (+ a1 a2))  ;; (* 2 3) folded to 6
```

The critical case is `(if (< x 0) (- 0 x) x)`:

```scheme
(if val (apply-k k (- a1 a2)) (apply-k k x))
```

The CPS continuation structure **survives** — the `if` with `apply-k` in both branches is the compiled CPS code. The interpreter's dispatch on `(eq? head 'if)` and continuation frame construction are gone, but the runtime branching and continuation passing remain. This is exactly what call/cc needs to work in compiled output.

### What's Eliminated vs. What Survives

| Eliminated | Survives |
|---|---|
| `meval`'s `cond` on expression type | Continuation frames `(list 'k-if ...)` |
| `apply-k`'s tag dispatch | `apply-k` calls (k is unknown) |
| `m-lookup`'s alist traversal | `mapply` for closures |
| `apply-builtin`'s name matching | Arithmetic on unknown values |
| `car`/`cdr` on known program lists | Comparisons on unknowns |
| `eq?` checks against known heads | CPS branching structure |
| Dead branches (`(if #t x y)` → x) | |

## The Algebra Connection

The Cayley table underlies all of this. The toy P1/P2/P3 demo (`examples/futamura.scm`) specializes an interpreter `(lam op (lam arg (dot op arg)))` that does Cayley table lookups:

```
P1: specialize(interp, Q·Q·Q·CAR)          → APPLY (constant)
P2: specialize(interp, Q·Q·Q·x)            → dot(Q, dot(Q, dot(Q, x)))
```

P1 folds to a value. P2 produces a dot-chain — compiled code with no lambdas and no applications, just table lookups. The same principle scales from the 1KB table to the full CPS evaluator.

## PE Extensions for P2

Two changes to the PE were needed for P2 to work:

1. **`list` form handling** — The CPS evaluator builds continuation frames with `(list 'k-if ...)`. The PE now builds lists even when some elements are unknown, so continuation frames can be constructed and `apply-k` can dispatch on the known tag.

2. **Precise residualization** — When a function body evaluates to generic `*unknown*` (the "I have no idea" sentinel), the PE residualizes the function call. But when it returns a *named* unknown like `(make-unknown 'x)`, that's a valid result — e.g., `m-lookup` returning an unknown variable's value. The PE now distinguishes these cases with `eq?` on `*unknown*` rather than `unknown?`.

## Running

```bash
cargo run -- examples/pe.scm               # PE tests (29 tests)
cargo run -- examples/futamura-real.scm     # P1 on real evaluator (10 tests)
cargo run -- examples/futamura-cps.scm      # P2 on CPS evaluator (23 tests)
```

## Verification

For fully-known programs, three paths agree:
- **Path A:** Direct Scheme evaluation
- **Path B:** CPS meta-evaluator interpretation
- **Path C:** PE specialization of CPS evaluator

For partially-known programs, verification by substitution: compile `(+ x 1)` with `x` unknown to get residual code, then compile `(+ 5 1)` fully to verify the residual would produce the same result (`6`).

## What This Means

A partial evaluator and a CPS interpreter, both written in Scheme, compose to form a compiler that:

1. Eliminates all interpretation overhead (expression dispatch, symbol lookup, builtin resolution)
2. Preserves CPS continuation structure (the `apply-k` calls and continuation frames survive)
3. Eliminates dead branches even with unknown values (`(if #t x y)` → `x`)
4. Folds known sub-expressions in mixed programs (`(+ (* 2 3) x)` folds the `6`)

The continuation structure surviving compilation is the key insight — it means call/cc, `reify`/`reflect`, and continuation surgery remain available in the compiled output. The interpreter vanishes, but the CPS plumbing stays.

This is the pipeline for fast CPS on embedded hardware:

```
Scheme program
    │  cps-compile (PE specializes CPS evaluator)
    ▼
Residual CPS code (no dispatch, continuations intact)
    │  --compile-lua
    ▼
Lua with CPS (Lua VM speed, GC'd, call/cc works)
```

The Cayley table governs type dispatch at every level. The PE removes the interpretation layer. The Lua backend makes it fast. And call/cc survives because the continuation frames are runtime data that the PE correctly residualizes.
