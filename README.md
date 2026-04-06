# WispyScheme

A 1KB Cayley table replaces branch-chain type dispatch with constant-time table indexing, encoding type validity, classification, and reflection in a single finite algebra while compiling to native Rust for `no_std` embedded targets.

Named after Wispy the guinea pig.

## What it is

An R4RS Scheme where type dispatch is branchless: instead of tag-bit branch chains (`if tag == T_PAIR { ... } else if ...`), every dispatch decision is a single table index into a 32×32 lookup table. The language is still dynamically typed — values still carry tags, and dispatch still happens at runtime — but the *mechanism* is a constant-time array lookup instead of a conditional cascade:

```
TABLE[CAR][T_PAIR] → T_PAIR   (valid: proceed to car field)
TABLE[CAR][T_STR]  → BOT      (type error → returned as a value, not an exception)
TABLE[CAR][T_SYM]  → BOT      (type error → returned as a value, not an exception)
TABLE[TAU][T_PAIR] → T_PAIR   (classify: it's a pair)
TABLE[TAU][T_SYM]  → T_SYM    (classify: it's a symbol)
```

The table is `const`, lives in flash on embedded targets, and is transparent to the optimizer. It is a semantic kernel for dispatch and reflection — the programmer can inspect the type-validity matrix at runtime via `dot`, `tau`, and `type-valid?`. The full language semantics (evaluation order, scoping, closures, continuations) live in the evaluator and compiler; the table captures which operations are valid on which types, how to classify values, and the algebraic relationships between operations.

The table's 12-element algebraic core was found by Z3 and is axiomatically equivalent to the [Kamea](https://github.com/stefanopalmieri/Kamea) project's Ψ₁₆ algebra (same axiom set satisfied, not isomorphic). The remaining 20 elements extend the core with R4RS type tags (pair, symbol, closure, string, vector, character, continuation, port) and special values (#t, eof, void).

Values are ribs (3-field structs: car, cdr, tag), following the [Ribbit](https://github.com/udem-dlteam/ribbit) model. Pairs, symbols, closures, strings, vectors, characters, continuations, and ports are all the same struct with a different tag byte.

## Performance

| Implementation | N-Queens(8) | Counter arithmetic |
|---|---|---|
| **C** (gcc -O2, bump alloc) | 96 µs | 0.017 µs |
| **WispyScheme → Rust** (rustc -O) | **136 µs** | **0.105 µs** |
| **LuaJIT** | 212 µs | 0.170 µs |
| **Chez Scheme** (10.3.0) | 228 µs | 0.213 µs |
| **SBCL** (native Common Lisp) | 440 µs | 0.187 µs |

On this cons-heavy, branch-heavy workload, compiled WispyScheme is 1.7x faster than Chez Scheme, 1.5x faster than LuaJIT, and 3.2x faster than SBCL. Chez Scheme is a production-quality R6RS compiler with full continuations, threads, and a generational GC — the comparison shows the cost/benefit of WispyScheme's simpler rib model on allocation-heavy workloads. Results are workload-sensitive; LuaJIT's trace compiler can outperform on tight numeric loops. All benchmarks on Apple M-series, single-threaded.

## Quick Start

```bash
cargo run                            # REPL
cargo run -- examples/fib.scm        # run a file
cargo run -- -e '(+ 1 2)'           # evaluate expression
cargo run -- --strict examples/fib.scm   # strict type checking
cargo run -- --compile examples/nqueens.scm > nqueens.rs  # compile to Rust
rustc -O -o nqueens nqueens.rs && ./nqueens   # native binary
cd lean && lake build                        # verify table proofs (14 theorems, ~6s)
cargo run -- examples/reflective-tower.scm   # run the self-hosted reflective tower
```

As a library:

```rust
use wispy_scheme::eval::Eval;

let mut ev = Eval::new();
ev.eval_str("(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))");
let result = ev.eval_str("(fib 10)"); // 55
```

## The Algebra Extension

Standard R4RS Scheme works as expected. The algebra is also available directly — the programmer can reach into the table:

```scheme
;; The table operation: CAYLEY[a][b]
(dot CAR T_PAIR)          ; → T_PAIR (car of pair is valid)
(dot CAR T_STR)           ; → BOT (car of string is a type error)

;; The classifier: what type is this value?
(tau (cons 1 2))          ; → T_PAIR
(tau "hello")             ; → T_STR
(tau 42)                  ; → BOT (fixnum, not a rib)

;; Query the algebra: is this operation valid on this type?
(type-valid? CAR T_PAIR)  ; → #t
(type-valid? CAR T_STR)   ; → #f

;; The retraction pair: Q and E are exact inverses on core elements
(dot E (dot Q CAR))       ; → CAR (round-trip)
(dot Q (dot E CAR))       ; → CAR (round-trip)

;; The Y fixed point: algebraic, not computed
(dot RHO (dot Y RHO))     ; → (dot Y RHO) (fixed point of ρ)

;; Build your own dispatcher from the table
(define (type-name x)
  (let ((t (tau x)))
    (cond ((= t T_PAIR) "pair")
          ((= t T_SYM)  "symbol")
          ((= t T_STR)  "string")
          (else          "other"))))

;; Enumerate valid operations for a type
(define (count-valid-ops type-tag)
  (let loop ((op 0) (count 0))
    (if (= op 12) count
        (loop (+ op 1)
              (+ count (if (type-valid? op type-tag) 1 0))))))
```

All 12 core elements (`TOP`, `BOT`, `Q`, `E`, `CAR`, `CDR`, `CONS`, `RHO`, `APPLY`, `CC`, `TAU`, `Y`) and 8 type tags (`T_PAIR`, `T_SYM`, `T_CLS`, `T_STR`, `T_VEC`, `T_CHAR`, `T_CONT`, `T_PORT`) are bound as constants. `dot`, `tau`, and `type-valid?` are the three primitives. Everything else is sugar.

BOT as a return value instead of an exception makes the algebra total: every input produces an output, no operation throws. This gives composability (chain operations without try/catch) and analyzability (the specializer can constant-fold through error cases). The tradeoff is silent error propagation — `(car "hello")` returns BOT and continues rather than crashing. The `--strict` flag restores Scheme's error-on-type-mismatch behavior for code that needs it. Philosophically this is closer to total functions with error values than to Scheme's dynamic error model.

## Architecture

```
src/
├── lib.rs          crate root
├── bin/wispy.rs    REPL, file runner, -e flag, --compile, --strict
├── table.rs        32×32 Cayley table (1KB const array), algebraic axiom tests
├── val.rs          Val = tagged pointer (fixnum | rib index)
├── heap.rs         Rib heap: uniform (car, cdr, tag) for all types
├── symbol.rs       Symbol interning (shared reader/evaluator)
├── reader.rs       S-expression parser
├── macros.rs       syntax-rules: pattern matching, ellipsis, template instantiation
├── eval.rs         Tree-walking evaluator, 104 builtins, tail call trampoline
├── cps.rs          CPS evaluator with first-class continuations (call/cc)
└── compile.rs      Scheme → Rust compiler (standalone native binaries)
```

Three execution paths:
- **Interpreter** (`eval.rs`): tail call optimization, 104 builtins, `(strict-mode)` / `(permissive-mode)` toggle
- **CPS evaluator** (`cps.rs`): first-class continuations, `call/cc`, re-entrant
- **Compiler** (`compile.rs`): Scheme → standalone Rust, 1.7x faster than Chez Scheme on nqueens(8). Self-tail-call → loop optimization, closure conversion, strings, characters, 55+ inlined builtins, and the algebra extension.

Self-hosted tools (all `.scm` files running on WispyScheme itself):
- **Specializer** (`examples/specialize.scm`): partial evaluator over algebraic expressions
- **Metacircular evaluator** (`examples/metacircular.scm`): defunctionalized CPS with inspectable continuations, reify/reflect
- **Transpiler** (`examples/transpile.scm`): IR → Rust code generator
- **Reflective tower** (`examples/reflective-tower.scm`): three-level Smith (1984) tower with continuation modification

## R4RS Coverage

### Implemented

**Special forms:** `quote`, `if`, `define`, `define-syntax`, `lambda` (multi-body), `set!`, `begin`, `cond`, `case`, `and`, `or`, `let`, `let*`, `letrec`, named `let`, `do`, `delay`, `quasiquote`/`unquote`/`unquote-splicing`

**Macros:** `syntax-rules` with pattern matching, ellipsis (`...`), literals, wildcards (`_`), and multiple clauses. Expansion in all three execution paths (interpreter, CPS, compiler).

**Control:** `call-with-current-continuation` (CPS evaluator), tail call optimization, rest parameters

**129 builtin procedures** covering arithmetic, comparison, pairs/lists, type predicates, booleans, equivalence, strings (including case-insensitive), vectors, characters (including case-insensitive), symbols, higher-order functions, port I/O, `read`, and `load`.

### R4RS status

Nearly complete. Remaining gaps:
- `dynamic-wind`
- Full macro hygiene (current `syntax-rules` is unhygienic)
- `call/cc` in the compiler (only the CPS evaluator supports `call/cc`)
- `char-ready?` (optional in R4RS)

See [`docs/r7rs-small-plan.md`](docs/r7rs-small-plan.md) for the path to R7RS-small compliance.

## The Cayley Table

The 32×32 table (1KB) is a finite algebra. All properties are Lean-proved (`lean/WispyScheme.lean`, 14 theorems, zero `sorry`, verified by `native_decide` in ~6 seconds):

- **Absorbers:** ⊤ (nil) and ⊥ (#f) are left absorbers
- **Retraction pair:** Q and E are mutual inverses on the core (quote/eval)
- **Classifier:** τ partitions the core into two boolean classes
- **Branch:** ρ dispatches on the classifier (conditional evaluation)
- **Composition:** cdr = ρ ∘ cons (second projection factors through branch)
- **Y fixed point:** Y(ρ) = ρ(Y(ρ)), non-absorber. The table contains a fixed-point *equation*, not unbounded computation. The algebra supplies the equation; the interpreter (or compiled loop) supplies the unbounded unfolding. Recursion is a collaboration between the finite table and the infinite evaluator, not a property of either one alone.
- **Extensionality:** all 32 rows are distinct
- **Type dispatch:** CAR × T_PAIR → valid, CAR × T_STR → error, etc.

The core satisfies the same axiom set as [Kamea's Ψ₁₆](https://github.com/stefanopalmieri/Kamea) (absorbers, retraction, classifier dichotomy, branch, composition, Y), making it axiomatically equivalent but not isomorphic (different carrier size, different table entries). The three independent capabilities carry over: self-representation (Q/E), self-description (τ), and self-execution (branch + composition).

### Extensibility

The table is frozen by default but extensible by design. The 32×32 grid uses 23 elements (12 core + 8 type tags + 3 specials); rows/columns 23-31 are unused. New types can be added by filling in those rows without touching the proven 12×12 core — the algebraic invariants (absorbers, retraction, classifier, Y) depend only on the core block. On embedded targets, the table can be flashed separately from firmware, giving different sensor configurations different algebra extensions without recompiling the evaluator. The Lean proofs cover the default table; a swapped or extended table operates correctly but without formal guarantees on the new entries.

## Self-Hosted Tools

Six Scheme programs that run on WispyScheme itself, ported from the [Kamea](https://github.com/stefanopalmieri/Kamea) project's Psi Lisp originals:

| File | What it does |
|---|---|
| `examples/algebra-smoke.scm` | 83 assertions validating absorbers, retraction, classifier, composition, Y fixed point |
| `examples/ir-lib.scm` | Shared 7-node tagged-pair IR (Atom, Var, Dot, If, Let, Lam, App) |
| `examples/specialize.scm` | Partial evaluator: constant-folds `dot`, cancels QE pairs, eliminates dead branches, beta-reduces |
| `examples/futamura.scm` | All three Futamura projections on the 32×32 algebra |
| `examples/metacircular.scm` | Defunctionalized CPS evaluator with 14 inspectable continuation types |
| `examples/transpile.scm` | IR → Rust code generator (emits standalone binaries with inlined Cayley table) |
| `examples/reflective-tower.scm` | Three-level Smith (1984) reflective tower |

**The reflective tower** demonstrates three levels grounded in the Cayley table:

- **Level 0:** User programs (fib, fact) run through the meta-evaluator
- **Level 1:** The meta-evaluator probes the 32×32 table to verify algebraic invariants (absorbers, retraction, composition, fixed points)
- **Level 2:** `(reify)` captures the current continuation as walkable data; the program navigates the continuation chain, swaps the then/else branches of a pending `if`, and `(reflect)`s into the modified future — the `if` takes the *opposite* branch from what the source code says

Every continuation is a tagged list, not a closure. The program can read, modify, and rewrite its own control flow.

**The Futamura projections** demonstrate the specializer eliminating all interpretation overhead:

```scheme
;; Three paths to the same result:
;;   Path A: direct table lookup          (dot Q (dot Q (dot Q CAR)))    → 8
;;   Path B: specialize(interp, program)  fully fold interpreter+program → 8
;;   Path C: compile then apply           specialize partial → dot chain → 8

;; The compiled output has 3 dots, 0 lambdas, 0 applications.
;; All interpretation overhead is gone.
```

```bash
cargo run -- examples/reflective-tower.scm   # three-level tower with branch swap
cargo run -- examples/algebra-smoke.scm      # 83 algebra assertions
cargo run -- -e '(load "examples/ir-lib.scm") (load "examples/specialize.scm") (load "examples/futamura.scm")'
```

## `no_std` Support

WispyScheme compiles in three configurations:

| Configuration | Cargo flags | Heap | Symbols | Use case |
|---|---|---|---|---|
| **std** (default) | `--features std` | `Vec<Rib>` (growable) | `Vec<(String, Val)>` | Desktop, servers |
| **alloc** | `--no-default-features --features alloc` | `Vec<Rib>` (growable) | `Vec<(String, Val)>` | WASM, custom allocators |
| **bare metal** | `--no-default-features` | `[Rib; 8192]` (fixed) | `[([u8; 48], u8, Val); 512]` (fixed) | RP2040, ESP32, cortex-m |

The table, value representation, reader, heap, and symbol interning all compile without `std` or `alloc`. The evaluators (`eval.rs`, `cps.rs`) and compiler (`compile.rs`) require `std` due to I/O and string formatting.

```bash
# Verify bare-metal build
cargo check --no-default-features --lib
```

## Future Work

- **MMTk Immix GC** as an optional feature (`features = ["gc"]`). The bump allocator is the default for `no_std` embedded targets. Long-running applications can opt into garbage collection via [MMTk](https://www.mmtk.io/). The Kamea project already has a working MMTk Immix binding that achieves 184 µs on N-Queens(8).

- **Compiler improvements.** Mutual tail recursion (currently only self-tail-calls are optimized), `call/cc` support in compiled output.

- **Embedded demo.** Run WispyScheme on an RP2040 or ESP32-C3: read sensor values, apply user-defined Scheme rules, actuate outputs. Upload new `.scm` files over serial without reflashing.

- **Self-hosted compiler.** The self-hosted transpiler (`examples/transpile.scm`) currently only handles the 7-node algebraic IR (Atom/Var/Dot/If/Let/Lam/App). Extending it to cover full R4RS Scheme — closures, tail calls, strings, builtins — would replace the Rust compiler (`compile.rs`) with a Scheme-in-Scheme compiler. It would still emit Rust (using `rustc` as a backend), but the compiler itself would be written in the language it compiles.

## Lineage

WispyScheme descends from the [Kamea](https://github.com/stefanopalmieri/Kamea) project's algebraic framework. The independence theorems (93 Lean theorems, zero `sorry`) are in [finite-magma-independence](https://github.com/stefanopalmieri/finite-magma-independence). The rib-based value model is inspired by [Ribbit](https://github.com/udem-dlteam/ribbit).

## License

MIT
