# WispyScheme: Paths to the Endgame

*Exploratory document — musings on architecture, not a roadmap.*

---

## The Goals

These are fixed stars to navigate by, not ordered milestones:

1. **Grounded reflective tower** — a la Kamea: a tower of interpreters that bottoms out at the algebra, not at an infinite regress.
2. **Branch swap demo** — swap the branching element in the Cayley table and watch program semantics change. The algebra is live, not decorative.
3. **The Cayley table is the dispatch mechanism** — not tag-bit branches, not polymorphic inline caches. One 32×32 lookup.
4. **First-class continuations** — `call/cc` with full reentry. The CPS architecture already represents continuations as closures; the question is whether to capture them.
5. **Chez-competitive performance** — on host, not necessarily bare metal. Chez has 35 years of engineering; closing the gap requires being deliberate about where cycles go.
6. **R7RS-small compatibility** — the whole standard, not a useful subset.
7. **Bare-metal RISC-V** — specifically ESP32-C6 class hardware. No OS, fixed heap, UART I/O. The entire Scheme world in a microcontroller.
8. **Futamura P3** — the specializer specialized on itself produces a compiler-compiler. The algebra's Lean proofs ground the dispatch layer.

---

## The Ground: What the Cayley Table Actually Is

Before the architecture, a moment to be precise about what we're building on.

The 32×32 table is not a lookup-table optimization of something else. It *is* the semantics. The 14 Lean-proved theorems are not documentation — they are the axioms from which the operational semantics of the language are derived. The absorber theorems describe what `nil` and `#f` do. The tau partition theorem describes how conditionals work. The Q/E retraction pair is quote and eval.

This matters for the reflective tower: when we say the tower is "grounded," we mean it terminates at the table itself. A table lookup needs no interpreter. The table *is* the bottom of the tower.

Everything above the table — ribs, closures, continuations, macros, the compiler — is defined by table entries. Swap entries, and you change what "above" means.

---

## The Tower: Reflectivity and What "Grounded" Means

### The standard reflective tower problem

A reflective tower gives you access to your own evaluator at runtime. Classic implementations (3-Lisp, Brown, Blond, Reflisp) have an infinite tower of meta-interpreters: level 0 runs at level 1, level 1 runs at level 2, etc. The question is: where does it stop?

The usual answer is "it stops at the host machine" which is unsatisfying — the tower bottoms out at something outside the system entirely.

### The algebraic answer

The Cayley table gives a *finite* ground. The tower looks like:

```
Level n:   Scheme interpreter (written in Scheme, evaluates level n-1)
  ...
Level 2:   Scheme interpreter (written in Scheme)
Level 1:   Algebra interpreter (evaluates algebraic expressions using the table)
Level 0:   The 32×32 table — a matrix of u8 values, no code, no evaluation needed
```

The table at Level 0 requires no evaluation because it is a finite object with no moving parts. A Lean proof about the table does not need a meta-theory about evaluation — it is pure combinatorics on a 1024-byte matrix.

This is what "grounded" means: you can always bottom-out at something that has been fully characterized by static proofs.

### The tower in practice

The practical tower for WispyScheme:

- **wispy-vm** (Stak fork): the evaluation engine for the tower levels. Runs Scheme with the Cayley table integrated into the VM's type dispatch.
- **rsc.scm**: the compiler, which is also a tower-level object — it is a Scheme program that can be run at any level of the tower.
- **The reflective tower entry point**: a Scheme program that, when given a program and an environment modification (e.g., a different table), evaluates the program in the modified semantics.

The Kamea port work is about wiring these together. The key insight is that `rsc.scm` already *is* a metacircular evaluator in a sense — it evaluates Scheme programs by compiling and running them. Making it reflective means making the table, the compilation strategy, and the continuation structure inspectable and modifiable at runtime.

---

## The Branch Swap Demo

This is the most visceral way to show the algebra is live. Here is what the demo should feel like:

```scheme
;; Normal semantics
(define (fact n) (if (= n 0) 1 (* n (fact (- n 1)))))
(display (fact 5))  ;; 120

;; Now swap the branching element (tau row) in the table at meta-level
(with-table (swap-row CAYLEY TAU)
  (display (fact 5)))  ;; diverges, or gives 0, depending on the swap
```

What you're doing: `tau` determines the boolean structure of the language. `(if test ...)` desugars to `(dot TAU (eval test))`, which partitions into true/false based on whether the result is in the "top" or "bottom" class of the tau partition. Swap tau's row, and `#f` becomes truthy or the partition inverts.

The deeper version swaps at a specific tower level, leaving the meta-level unchanged. Programs running at the object level are in a "non-standard model." The meta-level interpreter, running with the original table, can still observe and reason about the object level's behavior.

This is not a party trick. It is a live demonstration that the language's semantics are algebraic parameters, not hardwired constants.

### What needs to exist for this demo

1. The table must be a first-class runtime value, not a compile-time constant. Currently it is a `static CAYLEY: [[u8; 32]; 32]`.
2. A `with-table` form that evaluates its body in a modified-table context.
3. The metacircular evaluator (currently in wispy-vm's examples) must read from the active table, not a hardcoded one.
4. The tower must be deep enough to have a meta-level that holds the "real" table while the object level runs the swapped one.

The cleanest path: the metacircular evaluator in wispy-vm already uses Cayley-table dispatch internally. Making the table a parameter to the evaluator (rather than a global) is the key change.

---

## First-Class Continuations

### CPS already has them — almost

In rsc.scm's compilation model, every continuation is a `__cont_N` function. The current continuation `k` is always an explicit argument. `call/cc` in this model is:

```scheme
(call-with-current-continuation f)
;; CPS transforms to:
(f k k)
;; The continuation IS the second argument — you just pass it to f
```

This is escape-only `call/cc`. The closure you get can be called to abort back to the capture point, but you cannot re-enter it multiple times after the call stack has moved on. The reason: `__cont_N` functions are not self-contained snapshots of the computation; they expect to be called at most once in the right context.

### Full reentrant continuations

For full `call/cc`, a captured continuation must be re-invokable at any future point. This means the continuation closure needs to represent the entire remaining computation, including the trampoline state.

Two approaches:

**A. Stack-capture (SCP)**
Capture the C/Rust call stack into a heap buffer. GCC's `setjmp/longjmp` does a version of this. The problem: the Rust trampoline's stack at any given point includes Action values on the native call stack. Capturing those reliably is platform-specific and prevents the bare-metal target.

**B. Pure CPS (the right answer)**
In a fully CPS-compiled program, the native call stack depth is constant (the trampoline loop). Every continuation is already a heap-allocated closure. Reentry is just calling the closure again. The question is whether calling a continuation a second time after the dynamic context has moved causes problems.

In the current model, calling `__cont_N` twice causes no Rust-level issue — it is just a function call. The semantic question is whether the effects (I/O, mutation) replay correctly. For purely functional programs, full continuations fall out of CPS for free.

For programs with `set!` or I/O, delimited continuations (`reset`/`shift`) are usually the right tool — they capture only the relevant slice of the computation.

**The path forward for rsc.scm:**

1. `call/cc` for escape-only is one line of CPS: `(f k k)`. This is cheap and unlocks many patterns.
2. Full reentrant `call/cc`: verify that `__cont_N` closures are genuinely safe to call multiple times. For a CPS-compiled program with no mutable state, they already are.
3. Delimited continuations: add `reset`/`shift` to the CPS transform. These are more practically useful than unbounded `call/cc` for most reflective tower applications.

The reflective tower is actually *simpler* with delimited continuations than with full call/cc. Capturing the "rest of the current interpreter level" is exactly `reset`/`shift`.

---

## Performance: Closing the Gap with Chez

### Where we stand

Current rsc.scm benchmarks vs Chez (Apple M-series):

| Benchmark | rsc.scm (gen3) | Chez | Ratio |
|-----------|---------------|------|-------|
| fib(40) | ~4.7s | ~3.3s | 1.4× slower |
| tak(40,20,11) | ~10.7s | ~1.4s | 7.6× slower |
| sum | ~0.3s | ~2.4s | **8× faster** |
| ack | — | ~2.2s | — |

The fib gap is small and largely explained by missing fixnum propagation. The tak gap is large because `nqueens` and similar programs define lambdas via internal `define` that are not in `*global-ids*`, so the known-call optimization misses them.

### The fixnum problem

Every `(+ a b)` in the current compiled output does:
```rust
Val::fixnum(val_a.as_fixnum() + val_b.as_fixnum())
```

Two `.as_fixnum()` unwraps, one tag check, one pack. Chez, after type inference, emits:
```
add x0, x1, x2
```

One instruction. The gap on arithmetic-heavy benchmarks is almost entirely this.

**Fixnum propagation** is the single highest-leverage optimization remaining. Approach:
- During emission, track the "type context" of expressions: `Val`, `i64`, `bool`.
- When a subexpression is known to be fixnum (e.g., it is a literal, or the result of `+`/`*`/`-` applied to fixnum-typed args), emit in the `i64` context.
- Propagate through `if` branches: if both branches are fixnum, the `if` is fixnum.
- Box (wrap in `Val::fixnum`) only at the boundary — where a Val is actually needed.

This is what compile.rs's `emit_as_i64`/`emit_as_bool` do. Porting this to rsc.scm's emission pass would close the fib/tak gap significantly.

### Continuation inlining

Most continuations in CPS are linear — created in one place and called in exactly one other. These do not need to be heap-allocated closures:

```scheme
;; Before:
(let ((k (make_closure(17, env))))
  (dispatch_cps(f, [k, arg])))
  
;; After (inline k):
(let ((result (dispatch_cps(f, [arg]))))
  ; directly do what k would have done)
```

This is CPS-specific dead-closure elimination. The challenge is doing it in a single-pass emitter — you need to identify linear continuations before emitting them. In a two-pass approach: first pass marks linearity, second pass inlines.

The impact is large: every `(let ((x (f y))) body)` currently generates a continuation closure. Inlining these would halve allocation pressure on most benchmarks.

### Known-call completeness

The current known-call optimization only fires for top-level `define`d globals. But internal `define`s inside `lambda` bodies also produce named functions after closure conversion. If we extend `*global-ids*` to include all closure-converted function IDs (not just top-level ones), the optimization would fire for `nqueens`'s inner recursive functions too.

This is the difference between the 7.6× tak gap and a 2× gap.

### The Chez ceiling

Chez also has:
- Register allocation (the compiled output avoids some memory traffic)
- Inlining of small functions across call sites
- A mature generational GC with write barriers

The Cayley table dispatch is already competitive or faster than Chez on fixnum-heavy paths (sum: 8× faster). The algebraic story is not a liability; it is a potential advantage. The goal is to not give it back through avoidable boxing.

Realistic ceiling with fixnum propagation + continuation inlining + extended known-call: within 2× of Chez across the board, with wins on arithmetic-heavy benchmarks.

---

## Bare Metal: RISC-V and ESP32-C6

### The hardware target

ESP32-C6 specs:
- RISC-V RV32IMAC (no hardware float, Zicsr extension)
- 512KB SRAM, 4MB flash (typical configuration)
- No OS, no virtual memory, no dynamic linking
- UART0 for I/O

This rules out the allocator, the OS threading model, large stacks, and `std`. It also rules out rustc's default panic infrastructure.

### What already composes

The Cayley table has `#[no_std]` support today. The rsc.scm compiler already emits standalone Rust files. The gap:

1. The emitted runtime uses `Vec<Rib>` for the heap — needs replacement with a fixed-size `[Rib; N]` in BSS.
2. `display`/`write-char` write to stdout — needs replacement with UART writes.
3. `read-char`/`read` reads from stdin — needs UART reads or a compile-time program image.
4. Panic handler (`#[panic_handler]`) needed.

None of these are deep problems. They are boundary conditions.

### Two target modes

**Mode A: Compile-time program, runtime I/O**
The Scheme program is compiled to a RISC-V binary. The binary contains its own Rust runtime with a fixed heap. UART is the I/O channel. This is the simplest path and works today with minor changes.

```bash
rsc.scm --target riscv32imc-unknown-none-elf program.scm > program.rs
# Manual: change runtime to no_std, fixed heap, UART I/O
rustc --target riscv32imc-unknown-none-elf -C opt-level=2 program.rs -o program.elf
```

**Mode B: The Wispy VM on the ESP32**
Compile wispy-vm (Stak fork) for the ESP32. Now you have a Scheme REPL over UART. Load programs at runtime from the UART stream. This is the tower-on-a-chip approach.

The interesting thing: in Mode B, the reflective tower runs on 512KB of SRAM. The branch-swap demo runs on a microcontroller. The full tower — metal, algebra, evaluator, meta-evaluator — fits in a device that costs $3.

### Fixed-heap Cheney GC on bare metal

The Cheney GC already works with a fixed-size two-space array (SPACE_SIZE = 512K ribs). On bare metal, you declare both spaces in BSS:

```rust
static mut FROM: [Rib; SPACE_SIZE] = [Rib::NIL; SPACE_SIZE];
static mut TO: [Rib; SPACE_SIZE] = [Rib::NIL; SPACE_SIZE];
```

No allocator needed. The GC_BUDGET countdown already handles collection without `malloc`. This is exactly the right architecture for bare metal.

The ESP32-C6 has 512KB total SRAM. With two 128KB spaces (≈21K ribs each), you have room for a meaningful Scheme heap plus program code. For most programs that fit on a microcontroller, 21K ribs is generous.

---

## R7RS-small Compatibility

### What's missing (non-trivially)

The language feature gaps are known and manageable. The interesting design question is `define-syntax`/`syntax-rules` — hygienic macros.

**Option A: Port compile.rs's expander to Scheme**
compile.rs has a ~500-line Rust macro expander. Translating it to Scheme is mechanical. The advantage: known to work, ellipsis patterns and dotted tails already handled.

**Option B: Recursive macro expansion in the CPS pass**
Before CPS conversion, run a macro expansion pass over the AST. Macros are stored as transformation procedures (Scheme procedures, not Rust functions). This makes macros first-class and reflective — a macro can inspect and modify the compilation environment.

Option B is more powerful and fits the tower model better: macros are part of the tower, not a separate pre-pass. The cost is that you need to carefully scope the expansion environment.

### `define-library` and module system

R7RS-small has a module system (`define-library`, `import`, `export`). For single-file programs (what rsc.scm primarily targets), you can handle `import` by expanding to primitive lookups. A full module system with separate compilation is a bigger project, but probably not needed for the benchmark targets.

### Exception handling

`guard`/`raise`/`error` with `with-exception-handler`. In CPS, exceptions are continuation jumps. The handler is a captured continuation. This composes naturally with first-class continuations.

---

## Paths: Four Architectural Directions

These are not mutually exclusive. They are different slices of the problem.

### Path A: rsc.scm → compile.rs replacement (the current trajectory)

*Incrementally extend rsc.scm until it handles everything compile.rs does, then retire compile.rs.*

**The argument for:** Already working, clear progress metrics, self-hosting means the compiler can improve itself.

**The argument against:** The current CPS output is ~4× bigger than compile.rs output on some benchmarks (continuations have overhead). Getting to parity requires significant optimization work (continuation inlining, fixnum propagation). This is years of engineering to reproduce what compile.rs already does.

**What it unlocks:** Futamura P3. The reflective tower. First-class continuations. All the things that CPS enables and direct-style doesn't.

**Musing:** The compile.rs replacement is not the goal; it is a waypoint. The goal is a self-hosting compiler that can improve itself. Once rsc.scm can compile itself fast enough to run the specializer in reasonable time, the optimization passes can be written in Scheme and applied via P1/P2.

### Path B: wispy-vm as the tower substrate, rsc.scm as the AOT compiler

*wispy-vm handles interpretation and the reflective tower. rsc.scm handles ahead-of-time compilation for hot paths and production binaries.*

**The argument for:** Division of concerns. The tower is already running in wispy-vm. rsc.scm does not need to be a full interpreter; it just needs to be a good compiler.

**The argument against:** Two codebases to maintain, two runtimes, two type systems. Performance-critical paths need to cross the boundary.

**What it enables:** The branch-swap demo is natural here. wispy-vm runs the tower; rsc.scm compiles programs that run inside the tower at the object level.

**Musing:** The interesting version of this is "JIT as a tower level." wispy-vm runs interpreting; when a function becomes hot, a tower-level reflective procedure intercepts and compiles it via rsc.scm. This is a metacircular JIT. Computationally expensive but architecturally beautiful.

### Path C: Direct RISC-V emission

*Instead of Scheme → Rust → native, go Scheme → RISC-V directly.*

**The argument for:** Eliminates the rustc dependency. Natural for bare-metal targets. Smaller code (no Rust standard library overhead). Complete control over the register allocation.

**The argument against:** Enormous engineering investment. Register allocation, instruction selection, calling conventions — these are the hard parts of a compiler backend, and Rust/LLVM already solve them.

**The sweet spot:** Use rsc.scm to emit Rust for the host (where rustc is available and the optimization is valuable), and emit RISC-V assembly for the bare-metal target. Two backends in rsc.scm, same CPS IR.

**Musing:** The Cayley table in RISC-V assembly is just a 1KB `.rodata` constant. One `lb` instruction does the dispatch. At the RISC-V level, the table's algebraic elegance translates to actual instruction counts — no tag-bit branch trees, just one load. This might be the place where the algebraic architecture's performance advantage is most visible.

### Path D: Futamura-driven self-improvement

*Once rsc.scm is fast enough, specialize it on itself to produce an optimized compiler. Use the optimized compiler to compile programs faster. Iterate.*

**The argument for:** This is the theoretical endpoint of the project. All the other paths are preparation for this.

**The argument against:** Partial evaluation of a CPS compiler on itself is not obviously terminating. The specializer needs to handle higher-order functions without diverging. Kamea achieved this for Psi Lisp (a much smaller language); WispyScheme is harder.

**The concrete first step:** Specialize rsc.scm on a known program (e.g., the fib function). The specializer should see the fixed-input structure and eliminate the parsing pass, the CPS conversion of the known forms, etc. The residual should be the direct emission of the specific fib program's Rust code. If this works without divergence, it is P1 for the full language (not just the algebraic fragment).

**Musing:** The reason this is worth pursuing is not performance — it is *coherence*. A compiler that can improve itself, whose improvements are grounded in algebraic correctness proofs, and which runs its own meta-level via the same tower it compiles, is a complete object. It does not depend on something outside itself to be understood. The Cayley table at the bottom is finite and verified. Everything above it is in Scheme, compiled by itself, grounded in the table.

---

## The Synthesis: What Composition Looks Like

These paths are not alternatives — they are layers:

```
Futamura P3 (Path D)
  └─ rsc.scm with fixnum prop + cont inlining (Path A)
      └─ wispy-vm tower with branch-swap (Path B)
          └─ Cayley table (the ground)
              └─ RISC-V bare metal target (Path C)
```

Path C (RISC-V emission) is a *backend* for Path A (rsc.scm). It does not compete with the Rust backend; it extends it.

Path B (wispy-vm tower) is the *runtime environment* in which Path D (Futamura specialization) runs. The specializer lives in the tower; rsc.scm is one of the tower's occupants.

Path D (self-improvement) only becomes interesting after Path A closes the performance gap enough that specializing rsc.scm does not produce something slower than what you started with.

The sequence:
1. rsc.scm with fixnum propagation + continuation inlining → Chez-competitive
2. Branch-swap demo via wispy-vm tower + rsc.scm as object-level compiler
3. First-class continuations in rsc.scm → full call/cc, natural tower use
4. ESP32-C6 target via no_std Rust backend
5. Futamura P3 on full Scheme — the coherence completion

---

## Open Questions Worth Sitting With

**1. What is the right semantics for branch swap in a compiled setting?**

When rsc.scm compiles a program, the table entries are baked into the compiled output as `CAYLEY[i][j]` literal lookups. A `with-table` at runtime would need to either (a) re-interpret rather than re-compile, or (b) compile with an indirect table reference. Option (b) has performance cost. Option (a) means you need the metacircular evaluator to be running. What is the right design for a system that supports both compiled performance and live table mutation?

**2. Can the tower be grounded efficiently?**

Each tower level adds an interpretation overhead. Level 0 is a table lookup (one instruction). Level 1 adds the algebra interpreter overhead. Level 2 adds the Scheme evaluator overhead. For the reflective tower to be practical (not just demonstrable), the overhead at each level needs to be manageable. One answer: compilation at each level. The tower does not *execute* at each level; it *compiles down* through the levels until it hits something native. This is the Futamura picture.

**3. What does first-class call/cc mean for the bare-metal target?**

On the ESP32-C6 with a fixed 512KB heap, continuations that capture large amounts of state could exhaust memory quickly. This suggests the bare-metal target may want *delimited* continuations (`reset`/`shift`) rather than unbounded `call/cc`, even if the host target supports full `call/cc`. The design question is whether to parameterize this by target or by program.

**4. Is there a presentation of the branch-swap that is formally precise?**

The demo should be more than a live hack. The cleanest statement: "Given two algebras A₁ and A₂ that are identical except for the tau row, and a program P, we have `eval_A₁(P, env) ≠ eval_A₂(P, env)` in general, but `eval_A₁(specialize_A₁(P), ∅) = eval_A₁(P, ∅)` (the Futamura theorem holds separately for each algebra)." If you can state and prove this formally (even just for Psi Lisp), the demo becomes a theorem.

**5. What is the minimal Scheme runtime for RISC-V?**

A program like `(display (fib 30))` needs: fixnum arithmetic, function calls, tail calls, I/O. That is maybe 200 lines of RISC-V assembly. The Cayley table is 1KB of data. The entire runtime for fixnum-only programs fits in 4KB. This is the minimal viable bare-metal target — not full R7RS, but enough to be interesting. Map the minimal features needed for the branch-swap demo on bare metal: that is the RISC-V MVP.

---

## One More Ambitious Goal Worth Adding

**Lean-verified compilation.**

rsc.scm is currently an empirically correct compiler (verified by self-hosting bootstrap). The Lean proofs cover the algebra. The gap between the algebra proofs and the compiler's correctness is large.

The Psi Lisp formal semantics project (outlined in `docs/futamura-p3.md`) is the first step. But if the Lean-verified step is ever taken, the result would be:

*A self-hosting compiler, grounded in a Lean-verified finite algebra, whose compilation correctness is formally proved, that runs its own meta-level via a reflective tower, produces Chez-competitive native code, and fits on a $3 microcontroller.*

Each piece of that sentence is tractable independently. The combination has never been built.

---

*Written 2026-04-08. Goals as of: rsc.scm ~2200 lines, 9/12 r7rs-benchmarks, Cheney GC, known-call optimization, self-hosting at generation 2.*
