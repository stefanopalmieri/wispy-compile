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
