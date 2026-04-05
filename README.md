# WispyScheme

A small, finite algebra (1KB) replaces conventional runtime type dispatch, encoding control flow, reflection, and recursion in a single Cayley table while compiling to native Rust for `no_std` embedded targets.

Named after Wispy the guinea pig.

## What it is

An R4RS Scheme where type dispatch is data-driven rather than control-flow-driven. Each builtin operation is a row in a 32×32 lookup table. The operand's type tag indexes the column. The cell determines whether the operation is valid or a type error:

```
TABLE[CAR][T_PAIR] → T_PAIR   (valid: proceed to car field)
TABLE[CAR][T_STR]  → BOT      (type error)
TABLE[CAR][T_SYM]  → BOT      (type error)
TABLE[TAU][T_PAIR] → T_PAIR   (classify: it's a pair)
TABLE[TAU][T_SYM]  → T_SYM    (classify: it's a symbol)
```

This replaces the tag-bit branch chains in conventional Scheme implementations with constant-time table indexing. The table is `const`, lives in flash on embedded targets, and is transparent to the optimizer.

The table's 12-element algebraic core was found by Z3 and is axiomatically equivalent to the [Kamea](https://github.com/stefanopalmieri/Kamea) project's Ψ₁₆ algebra (same axiom set satisfied, not isomorphic). The remaining 20 elements extend the core with R4RS type tags (pair, symbol, closure, string, vector, character, continuation, port) and special values (#t, eof, void).

Values are ribs (3-field structs: car, cdr, tag), following the [Ribbit](https://github.com/udem-dlteam/ribbit) model. Pairs, symbols, closures, strings, vectors, characters, continuations, and ports are all the same struct with a different tag byte.

## Performance

| Implementation | N-Queens(8) | Counter arithmetic |
|---|---|---|
| **C** (gcc -O2, bump alloc) | 96 µs | 0.017 µs |
| **WispyScheme → Rust** (rustc -O) | **136 µs** | **0.105 µs** |
| **LuaJIT** | 212 µs | 0.170 µs |
| **SBCL** (native Common Lisp) | 440 µs | 0.187 µs |

On this cons-heavy, branch-heavy workload, compiled WispyScheme is 1.5x faster than LuaJIT and 3.2x faster than SBCL. Results are workload-sensitive; LuaJIT's trace compiler can outperform on tight numeric loops. All benchmarks on Apple M-series, single-threaded.

## Quick Start

```bash
cargo run                            # REPL
cargo run -- examples/fib.scm        # run a file
cargo run -- -e '(+ 1 2)'           # evaluate expression
cargo run -- --strict examples/fib.scm   # strict type checking
cargo run -- --compile examples/nqueens.scm > nqueens.rs  # compile to Rust
rustc -O -o nqueens nqueens.rs && ./nqueens   # native binary
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

BOT as a return value instead of an exception means type dispatch is data flow, not control flow. The programmer can query the capability matrix of the entire language with a 1KB lookup.

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
- **Compiler** (`compile.rs`): Scheme → standalone Rust, 1.5x faster than LuaJIT on nqueens(8). Self-tail-call → loop optimization, closure conversion, strings, characters, 55+ inlined builtins, and the algebra extension.

## R4RS Coverage

### Implemented

**Special forms:** `quote`, `if`, `define`, `define-syntax`, `lambda` (multi-body), `set!`, `begin`, `cond`, `case`, `and`, `or`, `let`, `let*`, `letrec`, named `let`, `do`, `delay`, `quasiquote`/`unquote`/`unquote-splicing`

**Macros:** `syntax-rules` with pattern matching, ellipsis (`...`), literals, wildcards (`_`), and multiple clauses. Expansion in all three execution paths (interpreter, CPS, compiler).

**Control:** `call-with-current-continuation` (CPS evaluator), tail call optimization, rest parameters

**114 builtin procedures** covering arithmetic, comparison, pairs/lists, type predicates, booleans, equivalence, strings (including case-insensitive), vectors, characters (including case-insensitive), symbols, higher-order functions, and I/O.

### Not yet implemented (R4RS)

- `read` (S-expression input from ports)
- Port I/O (`open-input-file`, `open-output-file`, `close-input-port`, `close-output-port`, `current-input-port`, `current-output-port`, `call-with-input-file`, `call-with-output-file`, `input-port?`, `output-port?`, `peek-char`, `char-ready?`)
- `load`
- `dynamic-wind`
- Full macro hygiene (current implementation is unhygienic)
- `call/cc` in the compiler (only the CPS evaluator supports `call/cc`)

See [`docs/r7rs-small-plan.md`](docs/r7rs-small-plan.md) for the path to R7RS-small compliance.

## The Cayley Table

The 32×32 table (1KB) is a finite algebra. All properties are Lean-proved (`lean/WispyScheme.lean`, 14 theorems, zero `sorry`, verified by `native_decide` in ~6 seconds):

- **Absorbers:** ⊤ (nil) and ⊥ (#f) are left absorbers
- **Retraction pair:** Q and E are mutual inverses on the core (quote/eval)
- **Classifier:** τ partitions the core into two boolean classes
- **Branch:** ρ dispatches on the classifier (conditional evaluation)
- **Composition:** cdr = ρ ∘ cons (second projection factors through branch)
- **Y fixed point:** Y(ρ) = ρ(Y(ρ)), non-absorber. This is an algebraic fixed point in the magma; unbounded recursion is a property of the interpreted language that this fixed point enables, not a property of the finite table itself.
- **Extensionality:** all 32 rows are distinct
- **Type dispatch:** CAR × T_PAIR → valid, CAR × T_STR → error, etc.

The core satisfies the same axiom set as [Kamea's Ψ₁₆](https://github.com/stefanopalmieri/Kamea) (absorbers, retraction, classifier dichotomy, branch, composition, Y), making it axiomatically equivalent but not isomorphic (different carrier size, different table entries). The three independent capabilities carry over: self-representation (Q/E), self-description (τ), and self-execution (branch + composition).

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

## Lineage

WispyScheme descends from the [Kamea](https://github.com/stefanopalmieri/Kamea) project's algebraic framework. The independence theorems (93 Lean theorems, zero `sorry`) are in [finite-magma-independence](https://github.com/stefanopalmieri/finite-magma-independence). The rib-based value model is inspired by [Ribbit](https://github.com/udem-dlteam/ribbit).

## License

MIT
