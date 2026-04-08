# WispyScheme

Scheme → Rust AOT compiler with branchless Cayley table type dispatch and optional semi-space Cheney GC. Compiles R7RS Scheme to standalone native binaries — beats Chez Scheme on triangl, fib, tak, and sum.

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

Type dispatch in the compiled output is branchless: instead of tag-bit branch chains, every dispatch decision is a single index into the 32×32 [Cayley table](https://github.com/stefanopalmieri/wispy-table) (`wispy-table` crate).

## Part of the Wispy ecosystem

| Repo | What | Install |
|------|------|---------|
| [**wispy-table**](https://github.com/stefanopalmieri/wispy-table) | 1KB Cayley table + Lean proofs + Z3 search | `cargo add wispy-table` |
| [**wispy-vm**](https://github.com/stefanopalmieri/wispy-vm) | Stak VM fork + REPL + examples + benchmarks | `cargo install --path wispy` |
| **wispy-compile** (this repo) | Scheme → Rust AOT compiler | `cargo install --path .` |

For interpreted execution, REPL, and running the self-hosted tools (reflective tower, partial evaluator, Futamura projections), use [wispy-vm](https://github.com/stefanopalmieri/wispy-vm).

## Language Support

**R4RS core:** `define`, `lambda` (including rest args), `if`, `cond`, `case`, `let`/`let*`/`letrec`, named `let`, `begin`, `and`/`or`, `quote`, `quasiquote`, `set!`, `do`, `define-syntax`/`syntax-rules` (with ellipsis and dotted tail patterns).

**R7RS extensions:** `case-lambda`, `define-record-type`, `values`/`call-with-values`, `guard`/`raise`/`error`/`with-exception-handler`, `define-library`/`import`, `call-with-current-continuation` (escape-only).

**Builtins:** 70+ inlined operations — arithmetic, comparisons, list ops (`map`, `for-each`, `apply`, `append`, `reverse`), strings, characters, vectors, `equal?`, type predicates, I/O (`display`, `write`, `read-char`, `read-line`, ports/files), and the three algebra primitives (`dot`, `tau`, `type-valid?`).

**First-class builtins:** Operators like `+`, `cons`, `car` can be passed as values (e.g., `(map + '(1 2) '(3 4))`).

**Vectors:** Flat contiguous layout — header rib + N element ribs. `vector-ref` and `vector-set!` are O(1) direct indexing. Cheney GC bulk-copies vectors as a single unit.

**Closures:** Full closure conversion with lambda lifting. Self-tail-call → loop optimization.

## Performance

### R7RS benchmarks (Apple M-series, single-threaded)

| Benchmark | Wispy (no GC) | Wispy (Cheney) | Chez | Winner |
|-----------|:------------:|:--------------:|:----:|--------|
| fib | 2.16s | 2.14s | 3.28s | **Wispy** 1.5x |
| tak | 1.02s | 1.03s | 1.38s | **Wispy** 1.4x |
| sum | 0.45s | 0.47s | 2.36s | **Wispy** 5.2x |
| ack | 4.88s | 4.62s | 2.24s | **Chez** 2.2x |
| deriv | 3.67s | 2.77s | 0.91s | **Chez** 4.0x |
| diviter | 4.65s | 4.08s | 1.26s | **Chez** 3.7x |
| divrec | 7.61s | 7.72s | 1.40s | **Chez** 5.4x |
| nqueens | 8.71s | 11.81s | 3.79s | **Chez** 2.3x |
| destruc | 2.85s | 3.76s | 1.27s | **Chez** 2.2x |
| triangl | 1.34s | 3.24s | 1.85s | **Wispy** 1.4x |
| takl | 4.06s | 4.08s | 3.39s | **Chez** 1.2x |
| primes | 2.32s | 3.10s | 0.65s | **Chez** 3.6x |

Benchmarks from [r7rs-benchmarks](https://github.com/ecraven/r7rs-benchmarks) with standard parameters. All 12 benchmarks pass in both modes. Wispy wins 4/12 (fixnum-heavy + vector), Chez wins 8/12 (allocation/list-heavy).

**No-GC mode** (grow-only heap) wins on pure fixnum recursion: 5.2× faster than Chez on sum, 1.5× on fib, 1.4× on tak, 1.4× on triangl. The gap on allocation-heavy benchmarks (divrec 5.4×, deriv 4.0×) is due to unbounded heap growth, no compaction, and unoptimized codegen (no type inference, no inlining).

**Cheney GC mode** uses liveness-based root elision: functions whose bodies (transitively) never allocate emit zero GC overhead. On fib/tak/sum/ack/takl/divrec, Cheney matches no-GC exactly. On deriv/diviter, Cheney *beats* no-GC (compaction improves cache locality). The remaining overhead on nqueens is from the benchmark harness calling closures via `call_val`, which the analysis conservatively treats as allocating.

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

- **Mutual tail recursion** — only self-tail-calls are optimized to loops. Mutually recursive functions in tail position use regular calls and can overflow the stack.
- **call/cc** — escape-only (non-reentrant). Full continuations would require a CPS transform.

## Future Work

Runtime changes (survive self-hosting):

- **Bare-metal RISC-V.** `--target no-std` with fixed-size heap arrays, no alloc crate, UART output.

Self-hosting:

- **Self-hosted compiler.** `examples/transpile.scm` is a self-hosted IR → Rust code generator ported from Kamea. The goal is to extend it to cover full Scheme, replacing `compile.rs` with Scheme-in-Scheme compiled by its own output.
- **Futamura P3.** Specialize the transpiler on a known program to produce a residual Rust-emitting program — a compiler generated from an interpreter.

Optimization passes (best written in the self-hosted compiler):

- **Type inference / specialization.** `(+ (car x) 1)` currently emits `.as_fixnum().unwrap()` on the car result. Propagating type information through the call graph would eliminate runtime type checks on provably-fixnum paths — the same optimization that makes Chez 2-5× faster on list-heavy benchmarks.
- **Cross-function inlining.** Lifted lambdas dispatch through `match code_id` in `dispatch_closure`. Inlining small closures at call sites would eliminate this indirect dispatch and enable further optimization by `rustc`.
- **Mutual tail recursion.** Trampoline or CPS transform for mutually recursive tail calls.
- **Full continuations.** CPS transform for reentrant `call/cc`.

## Lineage

WispyScheme descends from the [Kamea](https://github.com/stefanopalmieri/Kamea) project's algebraic framework. The independence theorems (93 Lean theorems, zero `sorry`) are in [finite-magma-independence](https://github.com/stefanopalmieri/finite-magma-independence). The VM is a fork of [Stak](https://github.com/raviqqe/stak), itself derived from [Ribbit](https://github.com/udem-dlteam/ribbit), with the Cayley table integrated into the VM.

## License

MIT
