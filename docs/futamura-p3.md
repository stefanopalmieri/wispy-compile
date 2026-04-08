# Futamura Projections and the Proof Ceiling

## Status

| Projection | Status |
|------------|--------|
| P1: `specialize(interpreter, program)` = compiled value | Done — `futamura.scm` (wispy-vm), three-path verified |
| P2: `specialize(interpreter, partial_program)` = compiled code | Done — residual IR has zero Lam/App nodes, verified |
| P3: `specialize(specialize, interpreter)` = compiler | One wire away empirically; not formally provable |

P1 and P2 work on the algebra: `specialize.scm` (wispy-vm) reduces algebraic expressions to
flat dot chains, and `transpile.scm` renders them as Rust. The two pieces are compatible.
P3 is the step of running `transpile-main` on the output of `specialize` to emit a standalone
Rust program with no interpreter overhead.

## What the Algebra Proofs Cover

The 14 Lean theorems in wispy-table (and the 130+ in DistinctionStructures/Kamea) prove
properties of the finite algebra: absorbers, the Q/E retraction pair, tau's partition of the
core, Y's fixed point, extensionality, type dispatch validity. These are purely algebraic.

At the dispatch layer, these theorems are load-bearing. The type dispatch theorems
("CAR applied to a pair type gives a valid result; CAR applied to a string type gives an error")
are essentially the typing rules for rib operations. The specializer's reductions on algebraic
expressions are trustworthy because the algebra's properties are proved.

## The Proof Ceiling

Kamea's DistinctionStructures repo reached P3 for Psi Lisp empirically
(`examples/psi_transpile_test.lisp`, `examples/psi_futamura_projections.lisp`) and explicitly
marks P3 as Empirical in CLAIMS.md — not Lean-proved. The documented reason:

> Futamura projections are properties of program transformations coupled to concrete table
> choices — they are not axiom-forced universals that the algebraic theorems can reach.

The specializer is a program in the metalanguage, not an object in the algebra. Proving P3
formally requires:

1. A formal semantics of the metalanguage the specializer is written in
2. A formal definition of the specializer as a mathematical function on programs
3. A bisimulation or logical-relations argument that `specialize(specialize, interpreter)`
   computes the same thing as the compiler for all inputs

None of these reduce to theorems about the Cayley table. The algebra proofs give you
correctness at the dispatch layer; the semantic correctness of P3 requires
CompCert-style compiler verification machinery, which is a substantial independent project
regardless of what sits underneath.

## What About the Rib Language?

A narrower target — prove P3 for the rib language (3-field ribs typed by the algebra)
rather than full Scheme — doesn't change the structural situation. The type dispatch theorems
would be load-bearing for type preservation, but the semantic correctness argument hits the
same wall at step 2. The rib language is a smaller target, not an easier proof.

## What Success Actually Looks Like

WispyScheme's P3 will be an empirical result, same as Kamea's. That is still meaningful:

- Kamea demonstrated P3 on a 16-element algebra with a minimal Lisp
- WispyScheme would demonstrate it on a 32-element algebra with R7RS Scheme
- The residual Rust programs would be competitive with `compile.rs` output
- The algebra's Lean proofs ground the dispatch layer correctness

The claim is not "we formally proved the compiler is correct end-to-end" but
"the interpreter vanishes when specialized on a known program, and the result
is native-competitive code." That is what Futamura originally demonstrated, and it
is what the DistinctionStructures work achieved for Psi Lisp.

## The Remaining Wire

The concrete P3 step for the algebraic fragment:

```scheme
(load "examples/wispy/ir-lib.scm")
(load "examples/wispy/specialize.scm")
(load "examples/wispy/transpile.scm")

;; Any fully-known program specializes to a flat dot chain...
(define residual (specialize some-program))

;; ...which transpile-main renders as a standalone Rust binary.
(transpile-main residual)
```

`specialize` already guarantees zero Lam/App nodes in the output (verified in
`futamura.scm`). `transpile-main` already handles exactly that input. The wire is
one function call.

The harder open question is P3 on the full language: whether specializing `rsc.scm`
on a known Scheme program eliminates the interpreter and produces output competitive
with `compile.rs`. That depends on whether the specializer handles closures and
higher-order functions without diverging — a general partial evaluation problem that
the algebra does not predetermine.

## Research Program: Formally Proving P3

The right order of attack is Psi Lisp first, then WispyScheme. The reasons are structural,
not just difficulty.

### Why Psi Lisp First

In Psi Lisp, values *are* algebra elements. There is no separate heap, no closures in the
traditional sense, no GC. A formal operational semantics has type `eval : Program → Env → Value`
where `Value = AlgebraElement` — already in Lean. The gap between the algebra proofs and
the language semantics is as small as it can be.

The Q/E retraction theorems are not just background facts for Psi Lisp: they are the
semantics of quote and eval in the language. The absorber theorems describe what happens
when you apply `nil` or `#f`. The existing 130+ Lean theorems in DistinctionStructures/Kamea
are closer to being a formal semantics of the language than they are for any other target.

For WispyScheme, values are ribs on a heap. The algebra types them but does not compute
them. A formal semantics must model the heap separately — a significant additional layer
that the algebra theorems do not reach.

### The Proof Structure

**Step 1: Operational semantics of Psi Lisp in Lean**

Formalize `eval` over the 16-element algebra. Values are algebra elements; environments
are association lists of element bindings; programs are quoted S-expressions encoded in
the algebra. This is tractable because the value domain is finite and already in Lean.

**Step 2: Formalize the metacircular evaluator**

`psi_metacircular.lisp` (DistinctionStructures) is already defunctionalized CPS —
continuations are explicit tagged data structures with 14 named types, not closures.
There is a body of literature on formally reasoning about defunctionalized interpreters
(Danvy, Reynolds). Prove the metacircular evaluator equivalent to the direct semantics
from Step 1.

Defunctionalized CPS is the right shape for a Lean formalization: you are reasoning
about a concrete inductive data type, not fighting with closure semantics.

**Step 3: Specializer correctness**

State and prove the specializer correct with respect to the Step 1 semantics:

```
∀ prog partialEnv completeEnv,
  extends completeEnv partialEnv →
  eval (specialize prog partialEnv) completeEnv = eval prog completeEnv
```

This is where the algebra theorems become load-bearing for the *proof*, not just the
*implementation*: the constant-folding reductions in `specialize.scm` are justified by
the Cayley table's algebraic properties, which are already proved in Lean.

**Step 4: P3 as a corollary**

Given Step 3, P3 — `specialize(specialize, interpreter)` computes the same results as
`interpreter` for all inputs — follows as a corollary by instantiating the correctness
theorem with the interpreter as the program and the specializer as the environment.

### What This Would Tell Us

If Step 3 goes through, the proof will have identified exactly which properties of the
algebra the specializer correctness argument depends on. That is a precise characterization
of what WispyScheme needs to inherit from its algebra for the proof to scale.

Formally proved P3 for any language would be a new result. The combination —
formally proved P3, grounded in a Lean-verified finite algebra, for a language whose
operational semantics is the algebra itself — would be a publishable contribution
independent of the WispyScheme engineering work.

### Scaling to WispyScheme

After Psi Lisp, the additional steps for WispyScheme are:

1. Formalize rib heap semantics in Lean (the algebra types ribs; the heap computes them)
2. Show the algebra's type dispatch theorems are the typing rules for rib operations
3. Re-run the specializer correctness argument at the rib level

Steps 2 and 3 would reuse the proof structure from Psi Lisp. Step 1 is the new work —
and knowing exactly what properties the Psi Lisp proof required tells you what the rib
heap formalization needs to provide.
