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
| [**wispy-vm**](https://github.com/stefanopalmieri/wispy-vm) | Stak VM fork + REPL + examples + benchmarks | `cargo install --path wispy` |
| **wispy-compile** (this repo) | Scheme → Rust AOT compiler | `cargo install --path .` |

For interpreted execution, REPL, running the self-hosted tools (reflective tower, partial evaluator, Futamura projections), and bootstrapping the self-hosted compiler (`examples/rsc.scm`), use [wispy-vm](https://github.com/stefanopalmieri/wispy-vm).

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

`examples/rsc.scm` is a self-hosted Scheme→Rust compiler written in Scheme (~1600 lines). It uses a CPS + closure conversion pipeline based on Feeley's 90-minute Scheme-to-C compiler: all function calls become tail calls through a trampoline, closures are lambda-lifted with cons-list environments, and every continuation's free variables are the precise live set.

The compiler reaches a **fixed point** at generation 2: the self-compiled binary produces identical output when compiling itself again. Bootstraps through [wispy-vm](https://github.com/stefanopalmieri/wispy-vm).

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

Remaining work: Cheney GC via CPS roots, optimization passes (type inference, inlining), and Futamura P3.

## Future Work

- **Cheney GC in the self-hosted compiler.** CPS makes GC root tracking systematic — every continuation's free variables are the precise live set. No shadow stack needed.
- **Type inference / specialization.** Propagating type information through the call graph would eliminate runtime type checks on provably-fixnum paths.
- **Cross-function inlining.** Inlining small closures at call sites would eliminate the `dispatch_cps` indirect dispatch.
- **Full continuations.** The CPS architecture already represents continuations as closures — `call/cc` just captures the current one.
- **Bare-metal RISC-V.** `--target no-std` with fixed-size heap arrays, no alloc crate, UART output.

## Lineage

WispyScheme descends from the [Kamea](https://github.com/stefanopalmieri/Kamea) project's algebraic framework. The independence theorems (93 Lean theorems, zero `sorry`) are in [finite-magma-independence](https://github.com/stefanopalmieri/finite-magma-independence). The VM is a fork of [Stak](https://github.com/raviqqe/stak), itself derived from [Ribbit](https://github.com/udem-dlteam/ribbit), with the Cayley table integrated into the VM.

## License

MIT
