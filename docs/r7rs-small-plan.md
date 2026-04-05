# R7RS-small Support Plan

WispyScheme currently targets R4RS. This document plans the path to R7RS-small compliance, following the model of Chibi Scheme (the de facto R7RS-small reference implementation).

## Current State

**What we have (R4RS):**
- 155 tests, 14 Lean theorems
- `syntax-rules` with ellipsis, literals, multiple clauses
- `call/cc` (CPS evaluator)
- TCO in compiler (self-tail-calls → loops)
- Closures in compiler (lambda lifting + free variable analysis)
- Strings, characters, vectors
- 104 builtin procedures
- Algebra extension (dot, tau, type-valid?)
- `no_std` bare-metal support
- REPL + CLI + compiler

**What R7RS-small adds over R4RS:**
- Library system (define-library, import, export)
- Exception handling (guard, raise, error objects)
- Records (define-record-type)
- Bytevectors
- Parameters (make-parameter, parameterize)
- Multiple values (values, call-with-values)
- 16 standard libraries
- cond-expand, include, syntax-error
- String/bytevector ports
- Various new procedures

## Phased Implementation

### Phase 1: Low-Hanging Fruit

Estimated effort: 1-2 sessions. No architectural changes.

**1.1 `define-record-type` (SRFI-9 style)**

Implement as a macro expanding to constructor, predicate, and accessors.
Uses a new rib tag (`T_RECORD = 23`, from our reserved slots).

```scheme
(define-record-type <point> (make-point x y) point?
  (x point-x)
  (y point-y set-point-y!))

;; Expands roughly to:
;; - make-point: allocates a rib (cons x y) with T_RECORD tag + type id
;; - point?: checks tag and type id
;; - point-x: car of the rib
;; - point-y: cdr of the rib (for 2-field records)
;; - For >2 fields: nested cons cells
```

**1.2 `case-lambda`**

Implement as a macro. Dispatches on argument count.

```scheme
(define-syntax case-lambda
  (syntax-rules ()
    ((case-lambda (params body ...) ...)
     (lambda args
       (let ((n (length args)))
         (cond ...))))))
```

Or implement natively for better error messages.

**1.3 `values` and `call-with-values`**

Multiple return values. The simplest implementation:
- `(values a b c)` → a rib with a special tag (`T_VALUES = 24`)
- `(call-with-values producer consumer)` → call producer, unpack the values rib, apply consumer

```scheme
(call-with-values (lambda () (values 1 2 3)) +)  ; → 6
```

**1.4 `cond-expand`**

Feature-based conditional compilation. We define WispyScheme's feature set:

```scheme
(cond-expand
  (wispy-scheme (display "Running on WispyScheme"))
  (chibi (display "Running on Chibi"))
  (else (display "Unknown")))
```

Features to advertise: `r7rs`, `wispy-scheme`, `no-std` (when applicable), `exact-closed`, `ieee-float` (if we add floats).

**1.5 Expose `read` as a Scheme procedure**

We already have a reader. Wrap it as a builtin that reads from the current input port (stdin initially).

```scheme
(read)  ; reads one S-expression from current-input-port
```

**1.6 `(scheme process-context)` basics**

```scheme
(command-line)              ; → list of command-line arguments
(exit)                      ; → terminate
(exit n)                    ; → terminate with status
(get-environment-variable)  ; → string or #f
```

**1.7 Missing small procedures**

- `boolean=?`, `symbol=?`
- `exact-integer?`
- `floor-quotient`, `floor-remainder`, `truncate-quotient`, `truncate-remainder`
- `square` (trivial: `(* x x)`)
- `string-copy`, `string-copy!`
- `vector-copy`, `vector-copy!`, `vector-fill!`
- `string->vector`, `vector->string`
- `string-for-each`, `vector-for-each`, `vector-map`
- `make-list`, `list-copy`
- `char-ci=?`, `char-ci<?`, etc. (case-insensitive)
- `string-ci=?`, `string-ci<?`, etc.
- `let-values`, `let*-values`

### Phase 2: Library System

Estimated effort: 2-3 sessions. This is the hardest piece.

**2.1 `define-library` syntax**

```scheme
(define-library (mylib utils)
  (import (scheme base))
  (export helper-fn)
  (begin
    (define (helper-fn x) (* x 2))))
```

**2.2 Design decisions**

| Decision | Options | Recommendation |
|---|---|---|
| Library resolution | File-based (Chibi) vs in-memory | File-based: `(foo bar)` → `foo/bar.sld` |
| Namespace isolation | Separate environments vs prefix mangling | Separate environments (cleaner) |
| Compilation unit | Library = one compiled module | Yes, matches Rust's module model |
| Built-in libraries | Hardcoded vs self-hosted | Hybrid: `(scheme base)` hardcoded, others in Scheme |

**2.3 Implementation plan**

1. **Library registry.** A `HashMap<LibraryName, Library>` mapping library names to their exported bindings.

2. **`import` resolution.** When the evaluator encounters `(import (scheme base))`:
   - Look up `(scheme base)` in the registry
   - If not found, search the library path for `scheme/base.sld`
   - Parse the `.sld` file, evaluate the `begin` body in a fresh environment
   - Cache the exported bindings

3. **`export` filtering.** Only exported names are visible to importers. `(only ...)`, `(except ...)`, `(rename ...)`, `(prefix ...)` modify the import set.

4. **Standard libraries.** Provide the 16 R7RS-small standard libraries:
   - `(scheme base)` — rebind our existing builtins
   - `(scheme write)` — display, write, write-shared, write-simple
   - `(scheme read)` — read
   - `(scheme char)` — char predicates and conversions
   - `(scheme eval)` — eval, environment
   - `(scheme file)` — file I/O (depends on Phase 3)
   - `(scheme lazy)` — delay, force, make-promise, promise?
   - `(scheme load)` — load
   - `(scheme process-context)` — exit, command-line, etc.
   - `(scheme time)` — current-second, current-jiffy
   - `(scheme case-lambda)` — case-lambda
   - `(scheme cxr)` — caar through cddddr
   - `(scheme repl)` — interaction-environment
   - `(scheme complex)` — optional (integer-only is valid)
   - `(scheme inexact)` — optional (integer-only is valid)
   - `(scheme r5rs)` — compatibility

5. **Compiler integration.** The compiler resolves imports during the `process` phase. Library code is inlined or linked into the compiled output.

**2.4 For the `no_std` target**

Libraries that depend on I/O (`scheme file`, `scheme load`, `scheme process-context`, `scheme time`) are gated behind `#[cfg(feature = "std")]`. The core libraries (`scheme base`, `scheme char`, `scheme lazy`, `scheme case-lambda`, `scheme cxr`) work without `std`.

### Phase 3: Exception Handling

Estimated effort: 1-2 sessions. Interacts with continuations.

**3.1 Core primitives**

```scheme
(with-exception-handler handler thunk)  ; install handler, run thunk
(raise obj)                             ; raise an exception (non-continuable)
(raise-continuable obj)                 ; raise, handler can return
(error message irritant ...)            ; create error object and raise
(error-object? obj)                     ; predicate
(error-object-message obj)              ; extract message string
(error-object-irritants obj)            ; extract irritants list
(file-error? obj)                       ; file-related error?
(read-error? obj)                       ; read-related error?
```

**3.2 `guard` syntax**

```scheme
(guard (var
        (test1 expr1)
        (test2 expr2)
        (else expr3))
  body ...)
```

Desugars to `with-exception-handler` + `call/cc`. The CPS evaluator handles this naturally since it already has continuations.

**3.3 Implementation**

Error objects: a new rib tag (`T_ERROR = 25`) with car = message (string), cdr = irritants (list).

`raise`: In the CPS evaluator, unwind to the nearest exception handler (a continuation). In the tree-walking evaluator, use Rust's `panic`/`catch_unwind` (similar to current `call/cc` hack) or switch to the CPS evaluator for programs that use exceptions.

`guard`: Implement as a macro expanding to `with-exception-handler` + `call/cc`.

### Phase 4: Bytevectors and Ports

Estimated effort: 2-3 sessions. New data types + I/O.

**4.1 Bytevectors**

New rib tag: `T_BYTEVEC = 26`. Stored as a rib where car = list of fixnum bytes, cdr = length (same pattern as strings but restricted to 0-255).

Procedures: `make-bytevector`, `bytevector`, `bytevector-length`, `bytevector-u8-ref`, `bytevector-u8-set!`, `bytevector-copy`, `bytevector-copy!`, `bytevector-append`, `utf8->string`, `string->utf8`.

**4.2 Ports**

Extend the existing `T_PORT` tag. A port rib carries:
- car = port-id (fixnum, indexes into a port table)
- cdr = direction (fixnum: 0 = input, 1 = output)

Port table (Rust side): `Vec<Box<dyn Read + Write>>` or similar, gated behind `std`.

Procedures: `open-input-file`, `open-output-file`, `close-input-port`, `close-output-port`, `read-char`, `peek-char`, `read-line`, `write-char`, `write-string`, `newline`, `char-ready?`, `input-port?`, `output-port?`, `port?`, `current-input-port`, `current-output-port`, `current-error-port`.

**4.3 String ports**

`open-input-string`, `open-output-string`, `get-output-string`. These are in-memory ports backed by a string buffer. Essential for testing and string processing.

### Phase 5: Parameters and Dynamic Binding

Estimated effort: 1 session.

```scheme
(define current-radix (make-parameter 10))

(current-radix)        ; → 10
(parameterize ((current-radix 16))
  (current-radix))     ; → 16
(current-radix)        ; → 10 (restored)
```

Implementation: parameters are closures with a thread-local value stack. `parameterize` pushes, body executes, then pops. In the CPS evaluator, this interacts with `dynamic-wind`.

### Phase 6: `dynamic-wind`

Estimated effort: 1 session. Needed for full `call/cc` correctness.

```scheme
(dynamic-wind before thunk after)
```

Ensures `before` runs on entry and `after` runs on exit, even when continuations jump in and out. Implementation: maintain a wind stack in the evaluator; `call/cc` captures it; invoking a continuation replays the wind/unwind sequence.

## Table Impact

The 32×32 table has reserved slots 23-31 (9 elements). R7RS-small needs:

| Slot | Use |
|---|---|
| 23 | T_RECORD (define-record-type) |
| 24 | T_VALUES (multiple values) |
| 25 | T_ERROR (error objects) |
| 26 | T_BYTEVEC (bytevectors) |
| 27 | T_PROMISE (delay/force, currently overloading T_CONT) |
| 28-31 | Available for future use |

The Cayley table rows for these new tags follow the same pattern as existing type tags: `TAU × T_RECORD → T_RECORD` (classify), `CAR × T_RECORD → BOT` (car of record is type error), etc. The Z3 search already filled rows 23-31 as constant functions, so adding type dispatch is a matter of updating those rows and re-running the Lean verification.

## Dependency Graph

```
Phase 1 (no deps)
  ├── define-record-type
  ├── case-lambda
  ├── values / call-with-values
  ├── cond-expand
  ├── read procedure
  ├── process-context
  └── missing small procedures

Phase 2 (depends on Phase 1)
  └── Library system (define-library, import, export)
      └── Standard library files (.sld)

Phase 3 (depends on CPS evaluator)
  └── Exception handling (guard, raise, error objects)

Phase 4 (depends on Phase 2 for library organization)
  ├── Bytevectors
  └── Ports (depends on std feature)
      └── String ports

Phase 5 (depends on Phase 3 for interaction with exceptions)
  └── Parameters (make-parameter, parameterize)

Phase 6 (depends on Phase 3 + Phase 5)
  └── dynamic-wind
```

## Effort Estimate

| Phase | Effort | Tests added | Cumulative |
|---|---|---|---|
| Phase 1 | 1-2 sessions | ~20 | ~175 |
| Phase 2 | 2-3 sessions | ~15 | ~190 |
| Phase 3 | 1-2 sessions | ~10 | ~200 |
| Phase 4 | 2-3 sessions | ~15 | ~215 |
| Phase 5 | 1 session | ~5 | ~220 |
| Phase 6 | 1 session | ~5 | ~225 |

Total: ~10-12 sessions from R4RS to R7RS-small.

## What We Can Skip (Per R7RS-small)

R7RS-small allows implementations to omit:
- Complex numbers (`(scheme complex)`)
- Inexact numbers (`(scheme inexact)`)
- Full Unicode (we can support ASCII subset)
- `transcript-on` / `transcript-off` (removed in R7RS)

Our integer-only numeric tower is valid. We document it as a feature: `(cond-expand (exact-closed ...) ...)`.

## Comparison with Chibi

| Aspect | Chibi Scheme | WispyScheme target |
|---|---|---|
| Language | C (17%) + Scheme (73%) | Rust (100%) |
| Size | ~50K lines | ~5K lines (current), ~10K estimated |
| VM | Bytecode interpreter | Table-driven eval + native compiler |
| GC | Mark-sweep | Bump allocator (+ optional MMTk Immix) |
| Numeric tower | Full (rational, complex) | Integer-only |
| Unicode | Full | ASCII (extensible) |
| Library resolution | File-based (.sld) | File-based (.sld), same convention |
| Embedding | C API | Rust crate (`no_std` compatible) |
| Unique feature | Reference implementation status | Algebraic type dispatch (Cayley table) |

## Success Criteria

WispyScheme is R7RS-small compliant when:
1. All 16 standard libraries are importable
2. `define-library` / `import` / `export` work
3. `define-record-type`, `guard`/`raise`, `values`/`call-with-values` work
4. R7RS-small test suite passes (use Chibi's test suite as reference)
5. The Lean file verifies any table changes
6. `no_std` still compiles for the core libraries
