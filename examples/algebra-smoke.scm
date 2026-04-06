;;; algebra-smoke.scm — Validate all algebra primitives from Scheme
;;;
;;; Run: cargo run -- examples/algebra-smoke.scm
;;;
;;; Tests the 32×32 Cayley table operations (dot, tau, type-valid?)
;;; and all 23 named element constants. This must pass before building
;;; any self-hosted tools on top of the algebra.

(define pass-count 0)
(define fail-count 0)

(define (check name expected actual)
  (if (equal? expected actual)
      (set! pass-count (+ pass-count 1))
      (begin
        (set! fail-count (+ fail-count 1))
        (display "FAIL: ")
        (display name)
        (display " expected ")
        (display expected)
        (display " got ")
        (display actual)
        (newline))))

;;; ── Element constants exist and have correct values ────────────────

(display "--- Element constants ---") (newline)
(check "TOP"    0  TOP)
(check "BOT"    1  BOT)
(check "Q"      2  Q)
(check "E"      3  E)
(check "CAR"    4  CAR)
(check "CDR"    5  CDR)
(check "CONS"   6  CONS)
(check "RHO"    7  RHO)
(check "APPLY"  8  APPLY)
(check "CC"     9  CC)
(check "TAU"   10  TAU)
(check "Y"     11  Y)
(check "T_PAIR" 12 T_PAIR)
(check "T_SYM"  13 T_SYM)
(check "T_CLS"  14 T_CLS)
(check "T_STR"  15 T_STR)
(check "T_VEC"  16 T_VEC)
(check "T_CHAR" 17 T_CHAR)
(check "T_CONT" 18 T_CONT)
(check "T_PORT" 19 T_PORT)
(check "TRUE"   20 TRUE)
(check "EOF"    21 EOF)
(check "VOID"   22 VOID)

;;; ── Absorbers: TOP and BOT absorb on the left ─────────────────────

(display "--- Absorbers ---") (newline)
(check "TOP*Q"    TOP (dot TOP Q))
(check "TOP*CAR"  TOP (dot TOP CAR))
(check "TOP*Y"    TOP (dot TOP Y))
(check "TOP*T_PAIR" TOP (dot TOP T_PAIR))
(check "BOT*Q"    BOT (dot BOT Q))
(check "BOT*CAR"  BOT (dot BOT CAR))
(check "BOT*Y"    BOT (dot BOT Y))
(check "BOT*T_STR" BOT (dot BOT T_STR))

;;; ── Retraction: Q and E are mutual inverses on the core ───────────

(display "--- QE Retraction ---") (newline)
(define core-elements (list Q E CAR CDR CONS RHO APPLY CC TAU Y))

(for-each
  (lambda (x)
    (check (string-append "E(Q(" (number->string x) "))")
           x (dot E (dot Q x)))
    (check (string-append "Q(E(" (number->string x) "))")
           x (dot Q (dot E x))))
  core-elements)

;;; ── Classifier: tau partitions core into TOP and BOT ───────────────

(display "--- Tau classifier ---") (newline)
;; tau on core elements returns either TOP(0) or BOT(1)
(for-each
  (lambda (x)
    (let ((result (dot TAU x)))
      (check (string-append "TAU(" (number->string x) ") in {TOP,BOT}")
             #t (or (= result TOP) (= result BOT)))))
  core-elements)

;;; ── Tau on runtime values ──────────────────────────────────────────

(display "--- Tau on values ---") (newline)
(check "tau(pair)"   T_PAIR (tau (cons 1 2)))
(check "tau(string)" T_STR  (tau "hello"))
(check "tau(char)"   T_CHAR (tau #\a))
(check "tau(vector)" T_VEC  (tau (make-vector 3 0)))

;;; ── Type dispatch: CAR × type → valid or BOT ──────────────────────

(display "--- Type dispatch ---") (newline)
(check "CAR valid on pair"   #t (type-valid? CAR T_PAIR))
(check "CAR error on string" #f (type-valid? CAR T_STR))
(check "CAR error on symbol" #f (type-valid? CAR T_SYM))
(check "CAR error on char"   #f (type-valid? CAR T_CHAR))

;;; ── Y fixed point ─────────────────────────────────────────────────

(display "--- Y fixed point ---") (newline)
(let ((y-rho (dot Y RHO)))
  (check "RHO(Y(RHO)) = Y(RHO)"  y-rho (dot RHO y-rho))
  (check "Y(RHO) is not TOP"      #f (= y-rho TOP))
  (check "Y(RHO) is not BOT"      #f (= y-rho BOT)))

;;; ── Extensionality: all 32 rows are distinct ──────────────────────

(display "--- Extensionality ---") (newline)
;; Check that no two distinct elements produce identical rows
;; by verifying a few known-distinct pairs
(check "Q row != E row" #f (and (= (dot Q TOP) (dot E TOP))
                                (= (dot Q BOT) (dot E BOT))
                                (= (dot Q Q)   (dot E Q))
                                (= (dot Q E)   (dot E E))))

;;; ── Composition: CDR = RHO . CONS ─────────────────────────────────

(display "--- Composition ---") (newline)
;; For core elements: dot(CDR, x) should equal dot(RHO, dot(CONS, x))
(for-each
  (lambda (x)
    (check (string-append "CDR(" (number->string x) ") = RHO(CONS(" (number->string x) "))")
           (dot CDR x) (dot RHO (dot CONS x))))
  core-elements)

;;; ── Summary ────────────────────────────────────────────────────────

(newline)
(display pass-count) (display " passed, ")
(display fail-count) (display " failed")
(newline)
(if (= fail-count 0)
    (display "All algebra smoke tests passed.")
    (display "SOME TESTS FAILED."))
(newline)
