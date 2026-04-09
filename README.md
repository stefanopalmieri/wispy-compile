# WispyScheme

Scheme → Rust AOT compiler built on a 1KB finite algebra. All type dispatch is a single table lookup — no tag-bit branches, no polymorphic inline caches — just a 32×32 [Cayley table](https://github.com/stefanopalmieri/wispy-table) with 14 Lean-proved theorems. Compiles R7RS Scheme to standalone native binaries with competitive performance.

Named after Wispy the guinea pig.

## What it does

Takes Scheme source and produces a standalone `.rs` file with inlined Cayley table, rib heap, and closure-converted code. No runtime dependencies — the output is a single Rust file you compile with `rustc`.

```bash
cargo run -- --compile bench/nqueens.scm > nqueens.rs
rustc -O -o nqueens nqueens.rs
./nqueens   # 92

# With semi-space Cheney GC (bounded memory):
cargo run -- --gc cheney --compile bench/nqueens.scm > nqueens.rs
```

Type dispatch in the compiled output is branchless: every dispatch decision is a single index into the Cayley table. The algebra replaces the tag-bit branch chains found in traditional Scheme implementations.

## Part of the Wispy ecosystem

| Repo | What | Install |
|------|------|---------|
| [**wispy-table**](https://github.com/stefanopalmieri/wispy-table) | 1KB Cayley table + Lean proofs + Z3 search | `cargo add wispy-table` |
| [**wispy-vm**](https://github.com/stefanopalmieri/wispy-vm) | Stak VM fork · REPL · self-hosted tools (specializer, Futamura tower, reflective tower, metacircular evaluator) | `cargo install --path wispy` |
| **wispy-compile** (this repo) | Scheme → Rust AOT compiler | `cargo install --path .` |

The self-hosted tool chain lives in wispy-vm under `examples/wispy/`:

| File | Role |
|------|------|
| `ir-lib.scm` | Shared 7-node algebraic IR (synced to `examples/ir-lib.scm` here) |
| `specialize.scm` | Partial evaluator for Cayley table IR — constant folding, dead branch elimination, beta reduction |
| `transpile.scm` | IR → Rust code generator (synced to `examples/transpile.scm` here) |
| `pe.scm` | General online partial evaluator for Scheme |
| `futamura.scm` | Futamura projections P1 and P2 on the algebra, with three-path verification |
| `futamura-real.scm` | P1 on a direct-style Scheme evaluator |
| `futamura-cps.scm` | P2 on the CPS metacircular evaluator |
| `reflective-tower.scm` | Reflective meta-interpreter tower |
| `metacircular.scm` | Metacircular Scheme interpreter |

`examples/ir-lib.scm` and `examples/transpile.scm` in this repo are synced copies of the wispy-vm originals, kept here so `rsc.scm` and the transpiler back-end can be developed and tested independently. The full Futamura pipeline (`specialize.scm` → `transpile.scm` → Rust) runs in wispy-vm. When `rsc.scm` matures to replace `compile.rs`, the self-hosted compiler will migrate there too, consolidating the complete self-hosting story in one place.

## Language Support

**R4RS core:** `define`, `lambda` (including rest args), `if`, `cond`, `case`, `let`/`let*`/`letrec`, named `let`, `begin`, `and`/`or`, `quote`, `quasiquote`, `set!`, `do`, `define-syntax`/`syntax-rules` (with ellipsis and dotted tail patterns).

**R7RS extensions:** `case-lambda`, `define-record-type`, `values`/`call-with-values`, `guard`/`raise`/`error`/`with-exception-handler`, `define-library`/`import`, `call-with-current-continuation` (escape-only).

**Builtins:** 70+ inlined operations — arithmetic, comparisons, list ops (`map`, `for-each`, `apply`, `append`, `reverse`), strings, characters, vectors, `equal?`, type predicates, I/O (`display`, `write`, `read-char`, `read-line`, ports/files), and the three algebra primitives (`dot`, `tau`, `type-valid?`).

**First-class builtins:** Operators like `+`, `cons`, `car` can be passed as values (e.g., `(map + '(1 2) '(3 4))`).

**Vectors:** Flat contiguous layout — header rib + N element ribs. `vector-ref` and `vector-set!` are O(1) direct indexing. Cheney GC bulk-copies vectors as a single unit.

**Closures:** Full closure conversion with lambda lifting. Self-tail-call → loop optimization.

## Performance

The point of these benchmarks is not "we beat Chez" — Chez Scheme has 35 years of engineering. The point is that a table-driven algebra produces competitive native code without the usual type-dispatch machinery. No polymorphic inline caches, no type-feedback JIT, no tag-bit branch chains — just a 1KB lookup table.

### R7RS benchmarks (Apple M-series, single-threaded)

| Benchmark | Wispy (no GC) | Wispy (Cheney) | Chez | Winner |
|-----------|:------------:|:--------------:|:----:|--------|
| fib | 1.96s | 1.97s | 3.28s | **Wispy** 1.7x |
| tak | 0.85s | 0.87s | 1.38s | **Wispy** 1.6x |
| sum | 0.29s | 0.31s | 2.36s | **Wispy** 8.1x |
| ack | 5.19s | 5.24s | 2.24s | **Chez** 2.3x |
| deriv | 2.01s | — | 0.91s | **Chez** 2.2x |
| diviter | 3.06s | 3.89s | 1.26s | **Chez** 2.4x |
| divrec | 6.12s | 7.69s | 1.40s | **Chez** 4.4x |
| nqueens | 7.63s | 11.64s | 3.79s | **Chez** 2.0x |
| destruc | 2.33s | 3.66s | 1.27s | **Chez** 1.8x |
| triangl | 1.17s | 3.10s | 1.85s | **Wispy** 1.6x |
| takl | 3.79s | 3.84s | 3.39s | **Chez** 1.1x |
| primes | 1.89s | 2.45s | 0.65s | **Chez** 2.9x |

Benchmarks from [r7rs-benchmarks](https://github.com/ecraven/r7rs-benchmarks) with standard parameters. All 12 benchmarks pass in no-GC mode; 11/12 pass in Cheney mode (deriv has a pre-existing GC bug). Wispy wins 4/12 (fixnum-heavy), Chez wins 8/12 (allocation/list-heavy).

**Where Wispy is faster** (fib, tak, sum, triangl): fixnum-heavy recursion where the Cayley table's branchless dispatch and fixnum propagation pay off — no type checks on the hot path, just raw i64 arithmetic and table lookups.

**Where Chez is faster** (deriv, nqueens, primes, etc.): allocation-heavy workloads where Chez's cross-function inlining and mature GC dominate. Wispy has expression-level type inference but not yet cross-function inlining — planned for the self-hosted compiler.

**Cheney GC mode** uses liveness-based root elision: functions whose bodies (transitively) never allocate emit zero GC overhead. On fib/tak/sum/ack/takl, Cheney matches no-GC exactly.

## Garbage Collection

The compiler supports two heap modes selected via `--gc`:

```bash
cargo run -- --compile file.scm              # grow-only heap (no GC, default)
cargo run -- --gc cheney --compile file.scm  # semi-space Cheney copying GC
```

**No GC** (`--gc none`): grow-only `Vec<Rib>` heap. Zero overhead, zero pauses, but memory is never reclaimed. Best for short-running programs and benchmarks where allocation pressure is low.

**Cheney GC** (`--gc cheney`): semi-space copying collector with 512K rib capacity per space. Uses a **shadow stack** for precise root tracking — all live `Val` variables (function parameters, let bindings, loop variables) are stored in a GC-visible `Vec<Val>` and read via `gc_load`/`gc_store`. The collector:

- Copies live objects breadth-first (Cheney scan pointer)
- Uses forwarding pointers (tag 255) for shared structure
- Protects `alloc_rib` arguments across GC via shadow stack push/pop
- Cleans up per-function via RAII `GcGuard` (Rust Drop trait)
- Truncates shadow stack at loop tops to prevent unbounded growth

## Architecture

```
src/
├── lib.rs          crate root (re-exports table, val, heap, symbol, reader, macros, compile)
├── bin/wispy.rs    compiler CLI (--gc none|cheney flag)
├── table.rs        re-export of wispy-table (32×32 Cayley table)
├── val.rs          Val = tagged pointer (fixnum | rib index)
├── heap.rs         rib heap: uniform (car, cdr, tag) for all types
├── symbol.rs       symbol interning
├── reader.rs       S-expression parser
├── macros.rs       syntax-rules: pattern matching, ellipsis, dotted tails, template instantiation
└── compile.rs      Scheme → Rust compiler (~5900 lines, includes both runtimes)
```

## The Cayley Table

The 32×32 table (1KB) is a finite algebra shared across all wispy repos via [wispy-table](https://github.com/stefanopalmieri/wispy-table). 14 Lean-proved theorems (zero `sorry`):

- **Absorbers:** top (nil) and bot (#f) are left absorbers
- **Retraction pair:** Q and E are mutual inverses on the core (quote/eval)
- **Classifier:** tau partitions the core into two boolean classes
- **Branch/Composition:** rho dispatches on tau; cdr = rho . cons
- **Y fixed point:** Y(rho) = rho(Y(rho)), non-absorber
- **Extensionality:** all 32 rows are distinct
- **Type dispatch:** CAR x T_PAIR → valid, CAR x T_STR → error

12 core elements, 8 R4RS type tags, 3 special values, 5 R7RS type tags (record, values, error, bytevector, promise), 4 unused slots. The core is axiomatically equivalent to [Kamea's Psi-16](https://github.com/stefanopalmieri/Kamea).

## `no_std` Support

The table, value representation, reader, heap, and symbol interning all compile without `std` or `alloc`. The compiler (`compile.rs`) requires `std`.

```bash
cargo check --no-default-features --lib
```

## Limitations

**compile.rs (direct-style):**
- **Mutual tail recursion** — only self-tail-calls are optimized to loops. Mutually recursive functions in tail position use regular calls and can overflow the stack.
- **call/cc** — escape-only (non-reentrant). Full continuations would require a CPS transform.

**rsc.scm (CPS)** resolves both limitations: all calls go through a trampoline (constant stack depth), and continuations are first-class closures.

## Self-Hosted Compiler

`examples/rsc.scm` is a self-hosted Scheme→Rust compiler written in Scheme (~2200 lines). It uses a CPS + closure conversion pipeline based on Feeley's 90-minute Scheme-to-C compiler: all function calls become tail calls through a trampoline, closures are lambda-lifted with cons-list environments, and every continuation's free variables are the precise live set.

The compiler reaches a **fixed point** at generation 2: the self-compiled binary produces identical output when compiling itself again. Bootstraps through [wispy-vm](https://github.com/stefanopalmieri/wispy-vm).

**GC:** rsc.scm emits a semi-space Cheney GC driven by a `GC_BUDGET` countdown — no shadow stack needed. Between trampoline steps only `f` + args are live; CPS makes the root set explicit. A generated `gc_roots_visit` visits all global vars and interned datums. A `GC_DEPTH` guard prevents GC from firing inside `scheme_map`/`scheme_for_each` where outer stack frames hold stale pointers.

**Known-call optimization:** When a tail call targets a compile-time-known global function, rsc.scm emits `__lambda_N(Val::NIL, args...)` directly, eliminating one `alloc_rib` (closure rib), one `Action` construction, and one `dispatch_cps` call per site. This gives 3.4× speedup on tak and 11% on fib.

```bash
# Compile a program (wispy-vm as host)
echo '(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))) (display (fib 30)) (newline)' \
  | wispy examples/rsc.scm > fib.rs && rustc -O -o fib fib.rs && ./fib  # 832040

# Self-compilation: rsc.scm compiles itself → gen1
wispy examples/rsc.scm < examples/rsc.scm > /tmp/rsc.rs
rustc -O -o /tmp/rsc /tmp/rsc.rs

# gen1 compiles rsc.scm → gen2 (fixed point: gen2 == gen3)
/tmp/rsc < examples/rsc.scm > /tmp/rsc2.rs
# diff /tmp/rsc.rs /tmp/rsc2.rs shows only gen1≠gen2 (host expansion diffs)
# but gen2 compiling rsc.scm produces identical output to gen2 itself
```

**What it compiles:** `define` (top-level and internal), `lambda`, `if`, `cond`, `let`/`let*`/`letrec`, named `let`, `begin`, `and`/`or`, `set!`, `quote`, `quasiquote`, closures, higher-order functions (`map`, `for-each`, `apply`), first-class primitives, strings, symbols, characters, `equal?`, `read`/`eof-object?`, `display`/`newline`/`write-char`, `error`.

**Pipeline:** S-expression → AST (tagged lists) → CPS conversion → lambda lifting / closure conversion → Rust emission (trampoline + `dispatch_cps` + `__lambda_N` functions).

Passes 9 of 12 r7rs-benchmarks (fib, sum, ack, tak, takl, nqueens, diviter, deriv, primes). Remaining work: type inference / fixnum propagation, continuation inlining, `call/cc`, multiple return values, macros, and wiring the specializer output into the P3 transpiler.

## Algebraic IR and Transpiler

Two companion files support Futamura-projection-based specialization over the Cayley table algebra. They operate on a different level than `rsc.scm`: where `rsc.scm` compiles general Scheme, these tools work exclusively with algebraic expressions — programs that compute by composing Cayley table lookups.

### `examples/ir-lib.scm` — Shared expression IR

Defines a 7-node tagged-pair representation for algebraic expressions:

| Node | Encoding | Meaning |
|------|----------|---------|
| `Atom(n)` | `(0 . n)` | constant algebra element (0–31) |
| `Var(x)` | `(1 . x)` | variable |
| `Dot(a, b)` | `(2 . (a . b))` | Cayley table lookup `a·b` |
| `If(t, c, a)` | `(3 . ...)` | conditional on `t != BOT` |
| `Let(x, v, b)` | `(4 . ...)` | local binding |
| `Lam(x, b)` | `(5 . ...)` | abstraction |
| `App(f, a)` | `(6 . ...)` | application |

Provides constructors (`mk-atom`, `mk-dot`, …), predicates, accessors, capture-avoiding substitution (`subst-expr`), and a pretty-printer (`ir-display`). Load this first — it is a dependency of `transpile.scm` and the specializer.

### `examples/transpile.scm` — IR → Rust code generator

Walks an IR expression tree and emits valid Rust source targeting the 32×32 Cayley table. This is the back-end for Futamura projections P2 and P3: the specializer reduces a program to a residual IR tree (no `Lam` or `App` nodes), and `transpile.scm` renders it as flat `u8` arithmetic over `CAYLEY[][]`.

Emission rules:
- `Atom(Q)` → named constant (`Q`, `CAR`, …) or `n_u8`
- `Dot(a, b)` → `CAYLEY[a as usize][b as usize]`
- `If(t, c, a)` → `if t != BOT { c } else { a }`
- `Let(x, v, b)` → `{ let v_x: u8 = v; b }`

`transpile-main` emits a complete standalone Rust program: element constants, the full 32×32 Cayley table literal, and a `fn main()` that evaluates the residual expression.

```bash
# Load both files and run the built-in tests
cargo run -- -e '(load "examples/ir-lib.scm") (load "examples/transpile.scm")'

# Or via wispy-vm
wispy -e '(load "examples/ir-lib.scm") (load "examples/transpile.scm")'
```

### Relationship to `rsc.scm`

| | `rsc.scm` | `transpile.scm` |
|-|-----------|-----------------|
| Input | Scheme source (s-expressions) | Algebraic IR (from `ir-lib.scm`) |
| Domain | General Scheme | Cayley table expressions only |
| Pipeline | CPS + closure conversion + trampoline | Direct tree walk |
| Output | Rust with a Scheme runtime | Rust doing pure `u8` table lookups |
| Role | The compiler proper | Back-end for the specializer's residual output |

`Lam` and `App` nodes are expected to be fully eliminated by the specializer before reaching `transpile.scm`. Bare lambdas in the input emit `0_u8` as a placeholder.

## Future Work

- **Futamura P3.** `specialize.scm` (wispy-vm) already produces Lam/App-free residual IR from a known program; `transpile.scm` already renders that IR as Rust. The remaining step is wiring the two: run `transpile-main` on the output of `specialize`, yielding a residual Rust program with zero interpreter overhead.
- **Type inference / specialization.** Propagating type information through the call graph would eliminate runtime type checks on provably-fixnum paths.
- **Cross-function inlining.** Inlining small closures at call sites would eliminate the `dispatch_cps` indirect dispatch.
- **Full continuations.** The CPS architecture already represents continuations as closures — `call/cc` just captures the current one.
- **Bare-metal RISC-V.** `--target no-std` with fixed-size heap arrays, no alloc crate, UART output.

## Lineage

WispyScheme descends from the [Kamea](https://github.com/stefanopalmieri/Kamea) project's algebraic framework. The independence theorems (93 Lean theorems, zero `sorry`) are in [finite-magma-independence](https://github.com/stefanopalmieri/finite-magma-independence). The VM is a fork of [Stak](https://github.com/raviqqe/stak), itself derived from [Ribbit](https://github.com/udem-dlteam/ribbit), with the Cayley table integrated into the VM.

## License

MIT
