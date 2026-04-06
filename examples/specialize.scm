;;; specialize.scm — Partial evaluator for Cayley table expressions
;;;
;;; Ported from Kamea's psi_specialize.lisp to WispyScheme Scheme.
;;;
;;; Optimizations:
;;;   - Constant folding: dot(Atom(a), Atom(b)) → Atom(CAYLEY[a][b])
;;;   - Dead branch elimination: if(Atom(BOT), t, e) → e; if(Atom(non-BOT), t, e) → t
;;;   - Let propagation: let x = Atom(v) in body → subst and specialize
;;;   - Beta reduction: ((lam x body) arg) → subst arg into body
;;;   - Lambda body specialization
;;;
;;; Requires: ir-lib.scm (loaded first)
;;; Run: cargo run -- -e '(load "examples/ir-lib.scm") (load "examples/specialize.scm")'

;;; ── The specializer ────────────────────────────────────────────────

(define (specialize expr)
  (cond
    ;; Atom — already a value
    ((is-atom? expr) expr)

    ;; Variable — can't reduce
    ((is-var? expr) expr)

    ;; Dot(a, b) — constant fold if both reduce to atoms
    ((is-dot? expr)
     (let ((a (specialize (dot-a expr)))
           (b (specialize (dot-b expr))))
       (if (and (is-atom? a) (is-atom? b))
           ;; Both atoms: look up the Cayley table
           (mk-atom (dot (atom-val a) (atom-val b)))
           ;; Otherwise: residualize
           (mk-dot a b))))

    ;; If — eliminate dead branch if test reduces to atom
    ((is-if? expr)
     (let ((test (specialize (if-test expr))))
       (if (is-atom? test)
           ;; Known test: BOT (1) = false, everything else = true
           (if (= (atom-val test) BOT)
               (specialize (if-else expr))
               (specialize (if-then expr)))
           ;; Unknown test: residualize both branches
           (mk-if test
                  (specialize (if-then expr))
                  (specialize (if-else expr))))))

    ;; Let — propagate known values
    ((is-let? expr)
     (let ((val (specialize (let-val expr))))
       (if (is-atom? val)
           ;; Known: substitute into body and specialize
           (specialize (subst-expr (let-var expr) val (let-body expr)))
           ;; Unknown: residualize
           (mk-let (let-var expr) val (specialize (let-body expr))))))

    ;; Lambda — specialize body
    ((is-lam? expr)
     (mk-lam (lam-var expr) (specialize (lam-body expr))))

    ;; App — beta reduce if function is a lambda
    ((is-app? expr)
     (let ((fn (specialize (app-fn expr)))
           (arg (specialize (app-arg expr))))
       (if (is-lam? fn)
           ;; Beta reduce: substitute arg into lambda body
           (specialize (subst-expr (lam-var fn) arg (lam-body fn)))
           ;; Otherwise: residualize
           (mk-app fn arg))))

    ;; Fallback
    (else expr)))

;;; ── Helper: extract atom value from a specialized result ───────────

(define (decode expr)
  (if (is-atom? expr)
      (atom-val expr)
      expr))

;;; ── Tests ──────────────────────────────────────────────────────────

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

(display "=== Specializer Tests ===") (newline)

;; Test 1: Constant folding — dot(Q, CAR) = Y (11)
(check "dot(Q,CAR)"
       (dot Q CAR)
       (decode (specialize (mk-dot (mk-atom Q) (mk-atom CAR)))))

;; Test 2: Nested dot — Q(Q(Q(CAR))) = APPLY (8)
(check "Q(Q(Q(CAR)))"
       (dot Q (dot Q (dot Q CAR)))
       (decode (specialize
         (mk-dot (mk-atom Q)
                 (mk-dot (mk-atom Q)
                         (mk-dot (mk-atom Q) (mk-atom CAR)))))))

;; Test 3: QE retraction — E(Q(CONS)) = CONS (6)
(check "E(Q(CONS))=CONS"
       CONS
       (decode (specialize
         (mk-dot (mk-atom E) (mk-dot (mk-atom Q) (mk-atom CONS))))))

;; Test 4: QE retraction — E(Q(CAR)) = CAR (4)
(check "E(Q(CAR))=CAR"
       CAR
       (decode (specialize
         (mk-dot (mk-atom E) (mk-dot (mk-atom Q) (mk-atom CAR))))))

;; Test 5: Dead branch — if(TOP, 42, 99) = 42 (TOP is not BOT, so true)
(check "if(TOP,42,99)"
       42
       (decode (specialize
         (mk-if (mk-atom TOP) (mk-atom 42) (mk-atom 99)))))

;; Test 6: Dead branch — if(BOT, 42, 99) = 99 (BOT = false)
(check "if(BOT,42,99)"
       99
       (decode (specialize
         (mk-if (mk-atom BOT) (mk-atom 42) (mk-atom 99)))))

;; Test 7: Let propagation — let x = Q in dot(x, CAR) = dot(Q, CAR) = Y
(check "let x=Q in dot(x,CAR)"
       (dot Q CAR)
       (decode (specialize
         (mk-let 'x (mk-atom Q)
                 (mk-dot (mk-var 'x) (mk-atom CAR))))))

;; Test 8: Beta reduction — ((lam x (dot E x)) (mk-atom Q)) = E(Q) = E (3)
(check "((lam x (dot E x)) Q)"
       (dot E Q)
       (decode (specialize
         (mk-app (mk-lam 'x (mk-dot (mk-atom E) (mk-var 'x)))
                 (mk-atom Q)))))

;; Test 9: Lambda body specialization
(let ((result (specialize (mk-lam 'x (mk-dot (mk-atom Q) (mk-atom E))))))
  (check "lam body fold"
         #t
         (and (is-lam? result)
              (is-atom? (lam-body result))
              (= (atom-val (lam-body result)) (dot Q E)))))

;; Test 10: Residualization — dot with unknown variable
(let ((result (specialize (mk-dot (mk-atom Q) (mk-var 'x)))))
  (check "dot(Q, var) residualizes"
         #t
         (is-dot? result)))

;; Test 11: Composition — CDR = RHO . CONS on a known element
;; dot(CDR, CAR) should equal dot(RHO, dot(CONS, CAR))
(check "CDR(CAR) = RHO(CONS(CAR))"
       (dot CDR CAR)
       (decode (specialize
         (mk-dot (mk-atom RHO)
                 (mk-dot (mk-atom CONS) (mk-atom CAR))))))

;; Test 12: Absorber — dot(TOP, anything) = TOP
(check "TOP absorbs"
       TOP
       (decode (specialize
         (mk-dot (mk-atom TOP) (mk-atom Y)))))

;; Test 13: Absorber — dot(BOT, anything) = BOT
(check "BOT absorbs"
       BOT
       (decode (specialize
         (mk-dot (mk-atom BOT) (mk-atom CONS)))))

;;; ── Futamura Projection 1 (preview) ───────────────────────────────
;;; The opcode interpreter: (lam op (lam arg (dot op arg)))
;;; Apply Q three times to CAR via the interpreter.

(display "=== Futamura Projection 1 (preview) ===") (newline)

(define interp (mk-lam 'op (mk-lam 'arg (mk-dot (mk-var 'op) (mk-var 'arg)))))

;; Program: interp(Q, interp(Q, interp(Q, CAR)))
(define prog
  (mk-app (mk-app interp (mk-atom Q))
          (mk-app (mk-app interp (mk-atom Q))
                  (mk-app (mk-app interp (mk-atom Q))
                          (mk-atom CAR)))))

(let ((result (specialize prog)))
  (check "Projection 1: interp(Q,Q,Q,CAR)"
         (dot Q (dot Q (dot Q CAR)))
         (decode result))
  (display "  direct:      ") (display (dot Q (dot Q (dot Q CAR)))) (newline)
  (display "  specialized: ") (display (decode result)) (newline))

;; QE round-trip via interpreter: interp(E, interp(Q, CONS)) = CONS
(define prog-qe
  (mk-app (mk-app interp (mk-atom E))
          (mk-app (mk-app interp (mk-atom Q))
                  (mk-atom CONS))))

(let ((result (specialize prog-qe)))
  (check "Projection 1: interp(E, interp(Q, CONS)) = CONS"
         CONS
         (decode result)))

;;; ── Projection 2 preview: partially known program ──────────────────
;;; Opcodes known, input unknown → residual dot chain

(define prog-partial
  (mk-app (mk-app interp (mk-atom E))
          (mk-app (mk-app interp (mk-atom Q))
                  (mk-var 'input))))

(let ((result (specialize prog-partial)))
  (display "  partial (E,Q,input): ") (ir-display result) (newline)
  ;; Should residualize to (dot E (dot Q input))
  (check "Projection 2: residual is dot"
         #t (is-dot? result)))

;;; ── Summary ────────────────────────────────────────────────────────

(newline)
(display pass) (display " passed, ")
(display fail) (display " failed") (newline)
(if (= fail 0)
    (display "All specializer tests passed.")
    (display "SOME TESTS FAILED."))
(newline)
