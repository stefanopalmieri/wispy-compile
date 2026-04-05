# WispyScheme

An R4RS Scheme grounded in a 1KB Cayley table. Compiles to native Rust. Targets `no_std` embedded.

Named after Wispy the guinea pig.

## What it is

A Scheme implementation where type dispatch is algebraic. Applying `car` to a pair, a string, or a number doesn't branch on a tag bit — it indexes into a 32×32 lookup table. The table encodes which operations are valid on which types. The table is `const`, lives in flash on embedded targets, and is transparent to the optimizer.

The table's 12-element algebraic core was found by Z3 and satisfies the same axioms as the [Kamea](https://github.com/stefanopalmieri/Kamea) project's Ψ₁₆ algebra: absorbers, extensionality, Q/E retraction, classifier dichotomy, branch, composition, and the Y fixed point.

Values are ribs (3-field structs: car, cdr, tag), following the [Ribbit](https://github.com/udem-dlteam/ribbit) model. Pairs, symbols, closures, strings, vectors, characters, continuations, and ports are all the same struct with a different tag byte.

## Performance

| Implementation | N-Queens(8) | Counter arithmetic |
|---|---|---|
| **C** (gcc -O2, bump alloc) | 96 µs | 0.017 µs |
| **WispyScheme → Rust** (rustc -O) | **136 µs** | **0.105 µs** |
| **LuaJIT** | 212 µs | 0.170 µs |
| **SBCL** (native Common Lisp) | 440 µs | 0.187 µs |

WispyScheme compiled to Rust is 1.5x faster than LuaJIT and 3.2x faster than SBCL on N-Queens(8).

## Quick Start

```rust
use wispy_scheme::eval::Eval;

let mut ev = Eval::new();
ev.eval_str("(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))");
let result = ev.eval_str("(fib 10)"); // 55
```

## Architecture

```
wispy-scheme/src/
├── table.rs      32×32 Cayley table (1KB const array), algebraic axiom tests
├── val.rs        Val = tagged pointer (fixnum | rib index)
├── heap.rs       Rib heap: uniform (car, cdr, tag) for all types
├── symbol.rs     Symbol interning (shared reader/evaluator)
├── reader.rs     S-expression parser
├── eval.rs       Tree-walking evaluator, 104 builtins, tail call trampoline
├── cps.rs        CPS evaluator with first-class continuations (call/cc)
└── compile.rs    Scheme → Rust compiler (standalone binaries)
```

Three execution paths:
- `eval.rs` — interpreter with tail call optimization (fast, no call/cc)
- `cps.rs` — CPS state machine with first-class continuations (R4RS compliant)
- `compile.rs` — generates standalone Rust programs (native speed)

## R4RS Coverage

### Implemented

**Special forms:** `quote`, `if`, `define`, `lambda` (multi-body), `set!`, `begin`, `cond`, `case`, `and`, `or`, `let`, `let*`, `letrec`, named `let`, `do`, `delay`, `quasiquote`/`unquote`/`unquote-splicing`

**Control:** `call-with-current-continuation` (CPS evaluator), tail call optimization, rest parameters

**104 builtin procedures** covering arithmetic, comparison, pairs/lists, type predicates, booleans, equivalence, strings, vectors, characters, symbols, higher-order functions, and I/O.

### Not yet implemented

- `syntax-rules` (hygienic macros)
- `read` (S-expression input from ports)
- Port I/O (`open-input-file`, `open-output-file`, `close-input-port`, `close-output-port`, `current-input-port`, `current-output-port`, `call-with-input-file`, `call-with-output-file`, `input-port?`, `output-port?`, `peek-char`, `char-ready?`)
- `load`
- Case-insensitive character and string comparisons (`char-ci=?`, `string-ci=?`, etc.)
- `dynamic-wind`
- `call/cc` in the compiler (only the CPS evaluator supports `call/cc`)

## The Cayley Table

The 32×32 table (1KB) is a finite algebra with a Z3-verified core:

- **Absorbers:** ⊤ (nil) and ⊥ (#f) are left absorbers
- **Retraction pair:** Q and E are mutual inverses on the core (quote/eval)
- **Classifier:** τ partitions the core into two boolean classes
- **Branch:** ρ dispatches on the classifier (conditional evaluation)
- **Composition:** cdr = ρ ∘ cons (second projection factors through branch)
- **Y fixed point:** Y(ρ) = ρ(Y(ρ)), non-absorber (unbounded recursion)
- **Extensionality:** all 32 rows are distinct
- **Type dispatch:** CAR × T_PAIR → valid, CAR × T_STR → error, etc.

The core sub-algebra embeds the same independence structure as [Kamea's Ψ₁₆](https://github.com/stefanopalmieri/Kamea): self-representation (Q/E), self-description (τ), and self-execution (branch + composition) are three independent capabilities.

## Future Work

- **MMTk Immix GC** as an optional feature (`features = ["gc"]`). The bump allocator is the default for `no_std` embedded targets. Long-running applications can opt into garbage collection via [MMTk](https://www.mmtk.io/). The Kamea project already has a working MMTk Immix binding that achieves 184 µs on N-Queens(8).

- **`no_std` heap variant.** Replace `Vec<Rib>` with a fixed-size `&mut [Rib]` buffer for bare-metal targets. The table and evaluator are already `no_std` compatible; the heap is the only blocker.

- **Lean verification.** Prove the 32×32 table's algebraic properties in Lean 4 via `native_decide` (1024 entries, well within capacity).

- **Compiler improvements.** Closure conversion, tail call optimization via loop, `call/cc` support in compiled output.

- **Embedded demo.** Run WispyScheme on an RP2040 or ESP32-C3: read sensor values, apply user-defined Scheme rules, actuate outputs. Upload new `.scm` files over serial without reflashing.

## Lineage

WispyScheme descends from the [Kamea](https://github.com/stefanopalmieri/Kamea) project's algebraic framework. The independence theorems (93 Lean theorems, zero `sorry`) are in [finite-magma-independence](https://github.com/stefanopalmieri/finite-magma-independence). The rib-based value model is inspired by [Ribbit](https://github.com/udem-dlteam/ribbit).

## License

MIT
