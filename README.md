# WispyScheme

Scheme → Rust AOT compiler with branchless Cayley table type dispatch. Compiles Scheme to standalone native binaries — 1.7× faster than Chez Scheme on nqueens(8).

Named after Wispy the guinea pig.

## What it does

Takes Scheme source and produces a standalone `.rs` file with inlined Cayley table, rib heap, and closure-converted code. No runtime dependencies — the output is a single Rust file you compile with `rustc`.

```bash
cargo run -- --compile bench/nqueens.scm > nqueens.rs
rustc -O -o nqueens nqueens.rs
./nqueens   # 92
```

Type dispatch in the compiled output is branchless: instead of tag-bit branch chains, every dispatch decision is a single index into the 32×32 [Cayley table](https://github.com/stefanopalmieri/wispy-table) (`wispy-table` crate).

## Part of the Wispy ecosystem

| Repo | What | Install |
|------|------|---------|
| [**wispy-table**](https://github.com/stefanopalmieri/wispy-table) | 1KB Cayley table + Lean proofs + Z3 search | `cargo add wispy-table` |
| [**wispy-vm**](https://github.com/stefanopalmieri/wispy-vm) | Stak VM fork + REPL + examples + benchmarks | `cargo install --path wispy` |
| **wispy-compile** (this repo) | Scheme → Rust AOT compiler | `cargo install --path .` |

For interpreted execution, REPL, and running the self-hosted tools (reflective tower, partial evaluator, Futamura projections), use [wispy-vm](https://github.com/stefanopalmieri/wispy-vm).

## Performance

| Implementation | N-Queens(8) | Counter arithmetic |
|---|---|---|
| **C** (gcc -O2, bump alloc) | 96 µs | 0.017 µs |
| **WispyScheme → Rust** (rustc -O) | **136 µs** | **0.105 µs** |
| **LuaJIT** | 212 µs | 0.170 µs |
| **Chez Scheme** (10.3.0) | 228 µs | 0.213 µs |
| **SBCL** (native Common Lisp) | 440 µs | 0.187 µs |

Gains come from branchless dispatch (table index vs. branch chain) and uniform rib representation. Results are workload-sensitive; LuaJIT's trace compiler can outperform on tight numeric loops. All benchmarks on Apple M-series, single-threaded.

## Architecture

```
src/
├── lib.rs          crate root (re-exports table, val, heap, symbol, reader, macros, compile)
├── bin/wispy.rs    compiler CLI
├── table.rs        re-export of wispy-table (32×32 Cayley table)
├── val.rs          Val = tagged pointer (fixnum | rib index)
├── heap.rs         rib heap: uniform (car, cdr, tag) for all types
├── symbol.rs       symbol interning
├── reader.rs       S-expression parser
├── macros.rs       syntax-rules: pattern matching, ellipsis, template instantiation
└── compile.rs      Scheme → Rust compiler (2609 lines)
```

The compiler handles: `define`, `lambda` (closure conversion), `if`, `cond`, `let`/`let*`/`letrec`, `begin`, `and`/`or`, `quote`, `set!`, `do`, `delay`, `quasiquote`, `define-syntax`/`syntax-rules`, self-tail-call → loop optimization, 55+ inlined builtins, and the three algebra primitives (`dot`, `tau`, `type-valid?`).

Does not yet handle: `call/cc`, mutual tail recursion, named `let` loops.

## The Cayley Table

The 32×32 table (1KB) is a finite algebra shared across all wispy repos via [wispy-table](https://github.com/stefanopalmieri/wispy-table). 14 Lean-proved theorems (zero `sorry`):

- **Absorbers:** ⊤ (nil) and ⊥ (#f) are left absorbers
- **Retraction pair:** Q and E are mutual inverses on the core (quote/eval)
- **Classifier:** τ partitions the core into two boolean classes
- **Branch/Composition:** ρ dispatches on τ; cdr = ρ ∘ cons
- **Y fixed point:** Y(ρ) = ρ(Y(ρ)), non-absorber
- **Extensionality:** all 32 rows are distinct
- **Type dispatch:** CAR × T_PAIR → valid, CAR × T_STR → error

12 core elements, 8 R4RS type tags, 3 special values, 9 unused slots for extension. The core is axiomatically equivalent to [Kamea's Ψ₁₆](https://github.com/stefanopalmieri/Kamea).

## `no_std` Support

The table, value representation, reader, heap, and symbol interning all compile without `std` or `alloc`. The compiler (`compile.rs`) requires `std`.

```bash
cargo check --no-default-features --lib
```

## Future Work

- **P2 → compiled pipeline.** Pipe Futamura P2 residual CPS code through `--compile` for native binaries with call/cc preserved.
- **Compiler improvements.** Mutual tail recursion, `call/cc` in compiled output, named `let`.
- **Self-hosted compiler.** Extend the self-hosted transpiler to cover full R4RS Scheme, replacing `compile.rs` with Scheme-in-Scheme.

## Lineage

WispyScheme descends from the [Kamea](https://github.com/stefanopalmieri/Kamea) project's algebraic framework. The independence theorems (93 Lean theorems, zero `sorry`) are in [finite-magma-independence](https://github.com/stefanopalmieri/finite-magma-independence). The VM is a fork of [Stak](https://github.com/raviqqe/stak), itself derived from [Ribbit](https://github.com/udem-dlteam/ribbit), with the Cayley table integrated into the VM.

## License

MIT
