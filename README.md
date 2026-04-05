# Kamea Scheme

An R4RS Scheme implementation grounded in a 64×64 Cayley table (4KB).

Type dispatch, small-value arithmetic, and type predicates are algebraic
operations — single table lookups with no branching. The table is the
runtime. Everything else is scaffolding.

## Architecture

```
64 elements = 6 bits per element, stored as bytes (2 spare bits for GC)
64×64 table = 4,096 entries × 1 byte = 4 KB

Element layout (tentative):
  0x00-0x06  algebraic core (⊤ ⊥ Q E car cdr cons branch classify ...)
  0x07-0x09  control (apply, call/cc, tail)
  0x0A-0x0F  type tags (pair, symbol, char, vector, string, closure)
  0x10-0x2F  immediate fixnums 0-31
  0x30-0x37  built-in symbols (lambda, if, define, quote, set!, begin, cond, let)
  0x38-0x3B  immediate chars or ports
  0x3C-0x3D  special (#t, #f, eof, void)
  0x3E-0x3F  reserved
```

## Design Principles

1. **R4RS compliance.** The target is the essential procedures of R4RS,
   with optional features (complex numbers, rationals, transcendentals)
   omitted per the spec's allowance.

2. **Table-driven type dispatch.** Applying `car` to a pair is a table
   lookup. Applying `car` to a fixnum is also a table lookup — the table
   row returns the error value. No tag-bit branching in the hot path.

3. **Immediate small values.** Fixnums 0-31, common symbols, and
   characters are algebraic elements. Arithmetic on small fixnums is
   a single table lookup.

4. **Bump allocator + optional GC.** The default allocator is a bump
   pointer (pointer increment, no free). MMTk Immix is available for
   workloads that need collection.

5. **`no_std` core.** The table and evaluator compile with zero
   dependencies on bare-metal Rust targets.

6. **Lean-verified sub-algebra.** The 7 computational core elements
   embed as a sub-algebra with the same independence properties as Ψ₁₆.

## R4RS Coverage

### Special Forms (primitive)
- [x] quote, lambda, if, set!, define (design only)

### Special Forms (derived — implemented as macros)
- [ ] cond, case, and, or, let, let*, letrec, begin, do, named let,
      delay, quasiquote

### Essential Procedures
- [ ] Booleans: not, boolean?
- [ ] Equivalence: eqv?, eq?, equal?
- [ ] Pairs/lists: pair?, cons, car, cdr, set-car!, set-cdr!, null?,
      list?, list, length, append, reverse, list-ref, memq, memv,
      member, assq, assv, assoc, caar..cddddr
- [ ] Symbols: symbol?, symbol->string, string->symbol
- [ ] Numbers: number?, integer?, exact?, inexact?, =, <, >, <=, >=,
      zero?, positive?, negative?, odd?, even?, max, min, +, *, -, /,
      abs, quotient, remainder, modulo, gcd, lcm, floor, ceiling,
      truncate, round, number->string, string->number
- [ ] Characters: char?, char=?, char<?, ..., char-alphabetic?,
      char-numeric?, char-whitespace?, char-upper-case?, char-lower-case?,
      char->integer, integer->char, char-upcase, char-downcase
- [ ] Strings: string?, make-string, string, string-length, string-ref,
      string-set!, string=?, string<?, ..., substring, string-append,
      string->list, list->string
- [ ] Vectors: vector?, make-vector, vector, vector-length, vector-ref,
      vector-set!, vector->list, list->vector
- [ ] Control: procedure?, apply, map, for-each, call/cc
- [ ] I/O: read, write, display, newline, read-char, write-char,
      peek-char, eof-object?, open-input-file, open-output-file,
      close-input-port, close-output-port, current-input-port,
      current-output-port, call-with-input-file, call-with-output-file,
      input-port?, output-port?, load

## Project Structure

```
src/
  table.py          — 64×64 Cayley table design + generator
  eval.py           — R4RS evaluator (table-driven)
  compile.py        — Scheme → C transpiler
  runtime.h         — C runtime (4KB table + allocator)
lean/
  KameaScheme.lean  — Algebraic properties of the 64-element table
examples/
  fib.scm           — (define (fib n) ...)
  nqueens.scm       — N-Queens for benchmark comparison
  r4rs-tests.scm    — R4RS compliance test suite
benchmarks/
  bench.c           — C baseline benchmarks
reference/
  psi_runtime.h     — Ψ₁₆ᶠ runtime (pattern reference)
  psi_lisp.py       — Ψ-Lisp interpreter (pattern reference)
  ...
docs/
  table_design.md   — Element allocation rationale
  r4rs_coverage.md  — Spec compliance tracking
```

## Lineage

Descended from the [Kamea](https://github.com/stefanopalmieri/Kamea)
project. The algebraic core (retraction pair, classifier dichotomy,
internal composition) embeds as a sub-algebra of the 64-element table.
Independence proofs:
[finite-magma-independence](https://github.com/stefanopalmieri/finite-magma-independence).
