# WispyScheme

WispyScheme has two core ideas: **(1)** branchless type dispatch via a finite Cayley table — every dispatch decision is a single array index, not a branch chain; **(2)** reifying that table as queryable program data — the programmer (and the specializer) can inspect, fold through, and reason about the type system at runtime. The table is 1KB, compiles to native Rust, and runs on `no_std` embedded targets.

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

The table's 12-element algebraic core was found by Z3 and is axiomatically equivalent to the [Kamea](https://github.com/stefanopalmieri/Kamea) project's Ψ₁₆ algebra (same axiom set satisfied, not isomorphic). The core includes a reify/reflect pair (Q/E) that are exact inverses — `E(Q(x)) = x` for all core elements — giving the algebra a built-in encoding/decoding capability distinct from the runtime reflective tower. The remaining 20 elements extend the core with R4RS type tags (pair, symbol, closure, string, vector, character, continuation, port) and special values (#t, eof, void).

Values are ribs (3-field structs: car, cdr, tag), following the [Ribbit](https://github.com/udem-dlteam/ribbit) model. Pairs, symbols, closures, strings, vectors, characters, continuations, and ports are all the same struct with a different tag byte.

## Performance

### Compiled output vs. other languages

| Implementation | N-Queens(8) | Counter arithmetic |
|---|---|---|
| **C** (gcc -O2, bump alloc) | 96 µs | 0.017 µs |
| **WispyScheme → Rust** (rustc -O) | **136 µs** | **0.105 µs** |
| **LuaJIT** | 212 µs | 0.170 µs |
| **Chez Scheme** (10.3.0) | 228 µs | 0.213 µs |
| **SBCL** (native Common Lisp) | 440 µs | 0.187 µs |

On this cons-heavy, branch-heavy workload, compiled WispyScheme is 1.7x faster than Chez Scheme, 1.5x faster than LuaJIT, and 3.2x faster than SBCL. The gains come primarily from branchless dispatch (table index vs. branch chain) and a uniform rib representation (no special cases for different heap object layouts). Results are workload-sensitive; LuaJIT's trace compiler can outperform on tight numeric loops. All benchmarks on Apple M-series, single-threaded.

### Cross-runtime: fib(30)

| Runtime | Mode | Time | vs. compiled |
|---|---|---|---|
| **WispyScheme → Rust** | AOT native | **5.3ms** | 1× |
| **LuaJIT** | JIT | 9.6ms | 1.8× |
| **WispyScheme → Lua** | transpiled | **71ms** | 13× |
| **Lua 5.5** | bytecode VM | 69ms | 13× |
| **MicroPython** | bytecode VM | 197ms | 37× |

The Lua backend (`--compile-lua`) matches handwritten Lua performance — transpiled Scheme runs at the same speed as hand-written Lua. On ESP32 (where LuaJIT is unavailable), this means WispyScheme compiled to Lua is the fastest scriptable option.

## Quick Start

```bash
cargo run                            # REPL
cargo run -- examples/fib.scm        # run a file
cargo run -- -e '(+ 1 2)'           # evaluate expression
cargo run -- --permissive examples/fib.scm   # permissive mode (type errors return BOT)
cargo run -- --compile examples/nqueens.scm > nqueens.rs  # compile to Rust
rustc -O -o nqueens nqueens.rs && ./nqueens   # native binary
cargo run -- --compile-lua examples/fib.scm | lua -       # compile to Lua, run immediately
cargo run -- examples/reflective-tower.scm   # run the self-hosted reflective tower
cd lean && lake build                        # verify table proofs (14 theorems, ~6s)
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

The algebra layer (`dot`, `tau`, `type-valid?`) is always total: every input produces an output, no operation throws. This gives the specializer and reflective tower composability and analyzability — they can fold through error cases because BOT is just another value.

The evaluator layer (`car`, `cdr`, etc. on actual values) is strict by default: `(car "hello")` raises an error, matching R4RS expectations. The REPL catches these errors and continues, so typos don't kill your session. The `--permissive` flag silences type errors (returns BOT instead), which is useful on embedded targets where panicking kills the device. The Scheme-level `(strict-mode)` and `(permissive-mode)` toggle at runtime.

## Architecture

```
src/
├── lib.rs          crate root
├── bin/wispy.rs    REPL, file runner, -e flag, --compile, --compile-lua
├── table.rs        32×32 Cayley table (1KB const array), algebraic axiom tests
├── val.rs          Val = tagged pointer (fixnum | rib index)
├── heap.rs         Rib heap: uniform (car, cdr, tag) for all types
├── symbol.rs       Symbol interning (shared reader/evaluator)
├── reader.rs       S-expression parser
├── macros.rs       syntax-rules: pattern matching, ellipsis, template instantiation
├── eval.rs         Tree-walking evaluator, 104 builtins, tail call trampoline
├── cps.rs          CPS evaluator with first-class continuations (call/cc)
├── compile.rs      Scheme → Rust compiler (standalone native binaries)
└── compile_lua.rs  Scheme → Lua compiler (runs on Lua VM, GC'd)
```

Four execution paths:
- **Interpreter** (`eval.rs`): tail call optimization, 104 builtins, strict by default (`--permissive` for embedded fault tolerance)
- **CPS evaluator** (`cps.rs`): first-class continuations, `call/cc`, re-entrant
- **Rust compiler** (`compile.rs`): Scheme → standalone Rust, 1.7x faster than Chez Scheme on nqueens(8). Self-tail-call → loop optimization, closure conversion, 55+ inlined builtins.
- **Lua compiler** (`compile_lua.rs`): Scheme → standalone Lua. Matches handwritten Lua performance. Includes compile-time `load`, symbol/string distinction, cons cells with GC, Cayley table as Lua array. The entire reflective tower (metacircular evaluator + reify/reflect + branch swap) compiles and runs on Lua — 12.6x faster than the interpreter.

Self-hosted tools (all `.scm` files running on WispyScheme itself):
- **Online PE** (`examples/pe.scm`): partial evaluator for Scheme — Futamura Projection 1 on a real interpreter
- **Specializer** (`examples/specialize.scm`): partial evaluator over algebraic IR expressions
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

The table is frozen by default but extensible by design. The 32×32 grid uses 23 elements (12 core + 8 type tags + 3 specials); rows/columns 23-31 are unused. New types can be added by filling in those rows without touching the proven 12×12 core — the algebraic invariants (absorbers, retraction, classifier, Y) depend only on the core block. On embedded targets, the table can be flashed separately from firmware, giving different sensor configurations different algebra extensions without recompiling the evaluator. The Lean proofs cover the default table; a swapped or extended table operates correctly but without formal guarantees on the extended portion.

## Self-Hosted Tools

Scheme programs that run on WispyScheme itself, ported from the [Kamea](https://github.com/stefanopalmieri/Kamea) project's Psi Lisp originals:

| File | What it does |
|---|---|
| `examples/algebra-smoke.scm` | 83 assertions validating absorbers, retraction, classifier, composition, Y fixed point |
| `examples/ir-lib.scm` | Shared 7-node tagged-pair IR (Atom, Var, Dot, If, Let, Lam, App) |
| `examples/specialize.scm` | Partial evaluator for algebraic IR: constant-folds `dot`, cancels QE pairs, eliminates dead branches |
| `examples/futamura.scm` | All three Futamura projections on the 32×32 algebra (three-path verification) |
| `examples/pe.scm` | Online partial evaluator for Scheme: folds arithmetic, branches, list ops, function calls |
| `examples/futamura-real.scm` | **Futamura Projection 1** on a real Scheme evaluator (four-path verification) |
| `examples/futamura-cps.scm` | **Futamura Projection 2** on the CPS evaluator — eliminates interpreter dispatch, preserves continuations |
| `examples/metacircular.scm` | Defunctionalized CPS evaluator with 14 inspectable continuation types |
| `examples/transpile.scm` | IR → Rust code generator (emits standalone binaries with inlined Cayley table) |
| `examples/reflective-tower.scm` | Three-level Smith (1984) reflective tower |

**Futamura Projection 1** — the interpreter vanishes:

```
specialize(interpreter, program) = compiled program
```

A direct-style Scheme evaluator (`deval`) is specialized with respect to a known fib program by the online partial evaluator (`pe.scm`). The PE unfolds all of deval's dispatch — the cond branches, car/cdr traversal of the AST, symbol lookup, environment extension — and folds everything to the bare result. Four paths to the same answer:

```
Path A  (direct Scheme):     (fib 8)                       → 21
Path B  (deval interpreter): (deval '(fib 8) env fns)      → 21
Path C  (PE specialized):    (pe deval {program=fib, n=8})  → 21
```

The classic PE benchmark also works: `power(base, 3)` with unknown base produces `(* base (* base (* base 1)))` — a straight-line multiplication chain with no recursion, no conditionals.

**Futamura Projection 2** — the CPS compiler:

```
specialize(PE, CPS-evaluator, program) = CPS compiler
```

All 16 functions of the CPS metacircular evaluator are registered in the PE. Specializing `meval` with a known program and unknown continuation produces residual CPS code where all interpreter dispatch has been eliminated:

```scheme
42                       → (apply-k k 42)      ;; constant folded
(+ (* 3 4) (- 10 5))    → (apply-k k 17)      ;; all dispatch eliminated
(if #t x y)             → (apply-k k x)        ;; dead branch eliminated
(if (< x 0) (- 0 x) x)  → (if val (apply-k k (- a1 a2)) (apply-k k x))
                          ;; CPS structure survives — call/cc still works
```

The CPS evaluator's 14 continuation types, mutual recursion (`meval`/`apply-k`/`mapply`), environment lookup, and builtin dispatch — all folded away. What remains is the bare computation plus the continuation plumbing that makes call/cc possible. See [`docs/futamura-projections.md`](docs/futamura-projections.md) for the full walkthrough.

**The reflective tower** demonstrates three levels grounded in the Cayley table:

- **Level 0:** User programs (fib, fact) run through the meta-evaluator
- **Level 1:** The meta-evaluator probes the 32×32 table to verify algebraic invariants (absorbers, retraction, composition, fixed points)
- **Level 2:** `(reify)` captures the current continuation as walkable data; the program navigates the continuation chain, swaps the then/else branches of a pending `if`, and `(reflect)`s into the modified future — the `if` takes the *opposite* branch from what the source code says

Every continuation is a tagged list, not a closure. The program can read, modify, and rewrite its own control flow.

**The reflective tower on Lua** — the entire tower (CPS evaluator + reify/reflect + branch swap) compiles to Lua via `--compile-lua` and runs 12.6x faster than the interpreter (16.7ms vs 210ms). All 45 tests pass, including the branch swap. Smith's 3-Lisp on a Lua VM with garbage collection.

```bash
cargo run -- examples/reflective-tower.scm                             # interpreted
cargo run -- --compile-lua examples/reflective-tower.scm | lua -       # compiled to Lua (12.6x faster)
cargo run -- examples/futamura-real.scm                                # Futamura P1
cargo run -- examples/futamura-cps.scm                                 # Futamura P2
cargo run -- examples/pe.scm                                           # PE tests
cargo run -- examples/algebra-smoke.scm                                # 83 algebra assertions
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

- **GC for the interpreter.** The tree-walking interpreter's heap grows without bound (400MB on fib(30)). A mark-and-sweep over the rib heap would fix this. The Lua backend sidesteps the problem entirely — Lua's GC manages cons cells.

- **P2 → Lua pipeline.** The Futamura P2 demo produces residual CPS code for partially-known programs. Piping that residual through `--compile-lua` would complete the compiler pipeline: Scheme → PE specializes CPS evaluator → residual CPS → fast Lua with call/cc preserved.

- **Bytecode VM.** The interpreter is 100x slower than Lua because it tree-walks. A bytecode compiler and register-based VM would close this gap. The Lua backend is the practical workaround.

- **ESP32 deployment.** The Lua backend targets [NodeMCU](https://nodemcu.readthedocs.io/) (Lua on ESP32). Compile Scheme to Lua on the workstation, upload `.lua` files over serial or MQTT. The Cayley table is a Lua array. No cross-compilation needed.

- **Compiler improvements.** Mutual tail recursion (currently only self-tail-calls are optimized), `call/cc` support in compiled Rust output, named `let` in both compiler backends.

- **Self-hosted compiler.** The self-hosted transpiler (`examples/transpile.scm`) currently only handles the 7-node algebraic IR. Extending it to cover full R4RS Scheme would replace `compile.rs` with a Scheme-in-Scheme compiler.

## Lineage

WispyScheme descends from the [Kamea](https://github.com/stefanopalmieri/Kamea) project's algebraic framework. The independence theorems (93 Lean theorems, zero `sorry`) are in [finite-magma-independence](https://github.com/stefanopalmieri/finite-magma-independence). The rib-based value model is inspired by [Ribbit](https://github.com/udem-dlteam/ribbit).

## License

MIT
