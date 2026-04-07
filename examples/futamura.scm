;;; futamura.scm — All three Futamura projections on the 32×32 algebra
;;;
;;; Ported from Kamea's psi_futamura_projections.lisp to WispyScheme.
;;;
;;; Demonstrates:
;;;   Projection 1: specialize(interpreter, program) = compiled value
;;;   Projection 2: specialize(interpreter, partial_program) = compiled code
;;;   Three-path verification: direct / projection 1 / projection 2 agree
;;;
;;; Run: cargo run -- examples/futamura.scm

(load "examples/ir-lib.scm")
(load "examples/specialize.scm")

(define pass 0)
(define fail 0)

(define (check name expected actual)
  (if (equal? expected actual)
      (set! pass (+ pass 1))
      (begin
        (set! fail (+ fail 1))
        (display "FAIL: ") (display name)
        (display " expected ") (display expected)
        (display " got ") (display actual) (newline))))

;;; ── The interpreter as an expression tree ──────────────────────────
;;; (lam op (lam arg (dot op arg)))
;;; Takes an opcode and an argument, computes via Cayley table lookup.

(define interp
  (mk-lam 'op (mk-lam 'arg (mk-dot (mk-var 'op) (mk-var 'arg)))))

;;; ════════════════════════════════════════════════════════════════════
;;; PROJECTION 1: specialize(interpreter, program) = value
;;;
;;; All inputs known → the specializer folds everything to a constant.
;;; ════════════════════════════════════════════════════════════════════

(display "=== PROJECTION 1: fully known programs ===") (newline)

;; Q applied three times to CAR: Q(Q(Q(CAR))) = APPLY (8)
(define p1-qqq
  (mk-app (mk-app interp (mk-atom Q))
          (mk-app (mk-app interp (mk-atom Q))
                  (mk-app (mk-app interp (mk-atom Q))
                          (mk-atom CAR)))))

(check "Q(Q(Q(CAR)))"
       (dot Q (dot Q (dot Q CAR)))
       (decode (specialize p1-qqq)))

;; QE retraction: E(Q(CONS)) = CONS (6)
(define p1-qe
  (mk-app (mk-app interp (mk-atom E))
          (mk-app (mk-app interp (mk-atom Q))
                  (mk-atom CONS))))

(check "E(Q(CONS)) = CONS"
       CONS
       (decode (specialize p1-qe)))

;; Composition: CDR(E(Q(CAR))) = CDR(CAR)
(define p1-comp
  (mk-app (mk-app interp (mk-atom CDR))
          (mk-app (mk-app interp (mk-atom E))
                  (mk-app (mk-app interp (mk-atom Q))
                          (mk-atom CAR)))))

(check "CDR(E(Q(CAR)))"
       (dot CDR (dot E (dot Q CAR)))
       (decode (specialize p1-comp)))

;; Absorber: TOP(anything) = TOP
(define p1-absorb
  (mk-app (mk-app interp (mk-atom TOP))
          (mk-app (mk-app interp (mk-atom Q))
                  (mk-atom Y))))

(check "TOP(Q(Y)) = TOP"
       TOP
       (decode (specialize p1-absorb)))

;;; ════════════════════════════════════════════════════════════════════
;;; PROJECTION 2: specialize(interp, partial_program) = compiled code
;;;
;;; Opcodes are KNOWN, input is UNKNOWN (a variable).
;;; The specializer eliminates all interpretation overhead, producing
;;; a residual dot-chain — the "compiled program."
;;; ════════════════════════════════════════════════════════════════════

(display "=== PROJECTION 2: partially known → compiled code ===") (newline)

(define unknown-x (mk-var 'x))

;; Q(Q(Q(x))) — unknown input, known opcodes
(define p2-qqq
  (mk-app (mk-app interp (mk-atom Q))
          (mk-app (mk-app interp (mk-atom Q))
                  (mk-app (mk-app interp (mk-atom Q))
                          unknown-x))))

(define compiled-qqq (specialize p2-qqq))

;; Should be a dot chain, not a constant
(check "Q(Q(Q(x))) residualizes to dot"
       #t (is-dot? compiled-qqq))

(display "  compiled form: ") (ir-display compiled-qqq) (newline)

;; Apply the compiled code to CAR → should get APPLY (8)
(define applied-qqq
  (specialize (subst-expr 'x (mk-atom CAR) compiled-qqq)))

(check "compiled Q(Q(Q(x))) applied to CAR"
       (dot Q (dot Q (dot Q CAR)))
       (decode applied-qqq))

;; E(Q(x)) — unknown input, retraction opcodes
(define p2-eq
  (mk-app (mk-app interp (mk-atom E))
          (mk-app (mk-app interp (mk-atom Q))
                  unknown-x)))

(define compiled-eq (specialize p2-eq))

(display "  compiled E(Q(x)): ") (ir-display compiled-eq) (newline)

;; Apply to CONS → should get CONS (retraction round-trip)
(define applied-eq
  (specialize (subst-expr 'x (mk-atom CONS) compiled-eq)))

(check "compiled E(Q(x)) applied to CONS = CONS"
       CONS
       (decode applied-eq))

;; Apply to RHO → should get RHO
(define applied-eq2
  (specialize (subst-expr 'x (mk-atom RHO) compiled-eq)))

(check "compiled E(Q(x)) applied to RHO = RHO"
       RHO
       (decode applied-eq2))

;;; ════════════════════════════════════════════════════════════════════
;;; THREE-PATH VERIFICATION
;;;
;;; Three routes to the same result — the essential Futamura insight:
;;;   Path A: Direct table lookup             dot(Q, dot(Q, dot(Q, CAR)))
;;;   Path B: Projection 1 (fully specialize) specialize(interp(Q,Q,Q,CAR))
;;;   Path C: Projection 2 (compile + apply)  specialize(compiled(Q,Q,Q), CAR)
;;; ════════════════════════════════════════════════════════════════════

(display "=== THREE-PATH VERIFICATION ===") (newline)

;; Path A: direct Cayley table
(define path-a (dot Q (dot Q (dot Q CAR))))

;; Path B: projection 1
(define path-b (decode (specialize p1-qqq)))

;; Path C: projection 2 — compile then apply
(define path-c (decode applied-qqq))

(display "  Path A (direct table):   ") (display path-a) (newline)
(display "  Path B (projection 1):   ") (display path-b) (newline)
(display "  Path C (projection 2):   ") (display path-c) (newline)

(check "Three paths agree (A=B)"  path-a path-b)
(check "Three paths agree (B=C)"  path-b path-c)

;; Second three-path test: E(Q(CONS))
(define path-a2 (dot E (dot Q CONS)))
(define path-b2 (decode (specialize p1-qe)))
(define applied-eq-cons
  (specialize (subst-expr 'x (mk-atom CONS) compiled-eq)))
(define path-c2 (decode applied-eq-cons))

(display "  E(Q(CONS)):") (newline)
(display "    A=") (display path-a2)
(display " B=") (display path-b2)
(display " C=") (display path-c2) (newline)

(check "E(Q(CONS)) three paths (A=B)" path-a2 path-b2)
(check "E(Q(CONS)) three paths (B=C)" path-b2 path-c2)

;;; ════════════════════════════════════════════════════════════════════
;;; PROJECTION 2 → COMPILER
;;;
;;; The compiled code (dot chain) IS the compiler's output.
;;; It contains no App nodes, no Lam nodes — just Dot and Atom/Var.
;;; All interpretation overhead has been removed.
;;;
;;; This demonstrates: specializing the interpreter with respect to
;;; the program's opcodes produces a specialized program that is
;;; strictly simpler (no lambdas, no applications) than the original.
;;; ════════════════════════════════════════════════════════════════════

(display "=== COMPILER OUTPUT STRUCTURE ===") (newline)

;; The compiled Q(Q(Q(x))) should contain no Lam or App nodes
(define (count-nodes pred expr)
  (cond
    ((is-atom? expr) (if (pred expr) 1 0))
    ((is-var? expr)  (if (pred expr) 1 0))
    ((is-dot? expr)  (+ (if (pred expr) 1 0)
                        (count-nodes pred (dot-a expr))
                        (count-nodes pred (dot-b expr))))
    ((is-if? expr)   (+ (if (pred expr) 1 0)
                        (count-nodes pred (if-test expr))
                        (count-nodes pred (if-then expr))
                        (count-nodes pred (if-else expr))))
    ((is-let? expr)  (+ (if (pred expr) 1 0)
                        (count-nodes pred (let-val expr))
                        (count-nodes pred (let-body expr))))
    ((is-lam? expr)  (+ (if (pred expr) 1 0)
                        (count-nodes pred (lam-body expr))))
    ((is-app? expr)  (+ (if (pred expr) 1 0)
                        (count-nodes pred (app-fn expr))
                        (count-nodes pred (app-arg expr))))
    (else 0)))

(check "compiled code has 0 lambdas"  0 (count-nodes is-lam? compiled-qqq))
(check "compiled code has 0 apps"     0 (count-nodes is-app? compiled-qqq))
(check "compiled code has 3 dots"     3 (count-nodes is-dot? compiled-qqq))

(display "  Q(Q(Q(x))) compiled: ")
(display (count-nodes is-dot? compiled-qqq)) (display " dots, ")
(display (count-nodes is-lam? compiled-qqq)) (display " lams, ")
(display (count-nodes is-app? compiled-qqq)) (display " apps")
(newline)

;;; ── Summary ────────────────────────────────────────────────────────

(newline)
(display pass) (display " passed, ")
(display fail) (display " failed") (newline)
(if (= fail 0)
    (display "All Futamura projection tests passed.")
    (display "SOME TESTS FAILED."))
(newline)
