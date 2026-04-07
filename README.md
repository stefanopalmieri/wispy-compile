# WispyScheme

Scheme → Rust AOT compiler with branchless Cayley table type dispatch and optional semi-space Cheney GC. Compiles R7RS Scheme to standalone native binaries — 1.7× faster than Chez Scheme on nqueens(8).

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

**Closures:** Full closure conversion with lambda lifting. Self-tail-call → loop optimization.

## Performance

### R7RS benchmarks (Apple M-series, single-threaded)

| Benchmark | Wispy (no GC) | Wispy (Cheney) | Chez | Winner |
|-----------|:------------:|:--------------:|:----:|--------|
| fib | 2.15s | 2.17s | 3.31s | **Wispy** 1.5x |
| tak | 1.03s | 1.04s | 1.39s | **Wispy** 1.3x |
| sum | 0.93s | 4.29s | 2.35s | **Wispy** 2.5x |
| ack | 4.92s | 8.90s | 2.33s | **Chez** 2.1x |
| deriv | 2.97s | 2.14s | 0.97s | **Chez** 3.1x |
| diviter | 4.65s | 3.84s | 1.06s | **Chez** 4.4x |
| divrec | 7.56s | 7.54s | 1.40s | **Chez** 5.4x |
| nqueens | 8.53s | 10.86s | 3.83s | **Chez** 2.2x |
| destruc | 2.83s | 3.28s | 1.26s | **Chez** 2.2x |
| triangl | 21.49s | 22.24s | 2.07s | **Chez** 10.4x |
| takl | 3.95s | 3.95s | 3.31s | **Chez** 1.2x |
| primes | 2.30s | 2.58s | 0.66s | **Chez** 3.5x |

Benchmarks from [r7rs-benchmarks](https://github.com/ecraven/r7rs-benchmarks) with standard parameters. Wispy wins 3/12 (fixnum-heavy), Chez wins 9/12 (allocation/list-heavy).

**No-GC mode** (grow-only heap) wins on pure fixnum recursion: 2.5× faster than Chez on sum, 1.5× on fib, 1.3× on tak. The gap on allocation-heavy benchmarks (triangl 10×, divrec 5.4×) is due to unbounded heap growth and no compaction.

**Cheney GC mode** uses liveness-based root elision: functions whose bodies (transitively) never allocate emit zero GC overhead. On fib/tak/takl/divrec, Cheney matches no-GC exactly. On deriv/diviter, Cheney *beats* no-GC (compaction improves cache locality). The remaining overhead on sum/ack/nqueens is from the benchmark harness calling closures via `call_val`, which the analysis conservatively treats as allocating.

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
└── compile.rs      Scheme → Rust compiler (~5300 lines, includes both runtimes)
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
- **Symbols at runtime** — `symbol->string` / `string->symbol` are not yet supported (symbols exist only at compile time).

## Future Work

- **Self-hosted compiler.** `examples/transpile.scm` is a self-hosted IR → Rust code generator ported from Kamea. The goal is to extend it to cover full Scheme, replacing `compile.rs` with Scheme-in-Scheme compiled by its own output.
- **Futamura P3.** Specialize the transpiler on a known program to produce a residual Rust-emitting program — a compiler generated from an interpreter.
- **Mutual tail recursion.** Trampoline or CPS transform for mutually recursive tail calls.
- **Full continuations.** CPS transform for reentrant `call/cc`.
- **GC optimization.** The Cheney GC shadow stack instruments every function (gc_push/gc_load for all params). Fixnum-only functions don't need this — detecting and skipping shadow stack for non-allocating paths would close the 2-5× overhead gap on numeric benchmarks.
- **Bare-metal RISC-V.** `--target no-std` with fixed-size heap arrays, no alloc crate, UART output.

## Lineage

WispyScheme descends from the [Kamea](https://github.com/stefanopalmieri/Kamea) project's algebraic framework. The independence theorems (93 Lean theorems, zero `sorry`) are in [finite-magma-independence](https://github.com/stefanopalmieri/finite-magma-independence). The VM is a fork of [Stak](https://github.com/raviqqe/stak), itself derived from [Ribbit](https://github.com/udem-dlteam/ribbit), with the Cayley table integrated into the VM.

## License

MIT
