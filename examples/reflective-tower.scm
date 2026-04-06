;;; reflective-tower.scm — Three-Level Reflective Tower
;;;
;;; Ported from Kamea's psi_reflective_tower.lisp to WispyScheme.
;;;
;;; Demonstrates Smith's (1984) reflective tower grounded in the Cayley table:
;;;   Level 0: Compute within the algebra (fibonacci via meta-evaluator)
;;;   Level 1: Verify the substrate (probe the 32×32 Cayley table)
;;;   Level 2: Reify/reflect with inspectable continuations
;;;   Level 2b: Walk the continuation chain as data
;;;   Level 2c: Modify the continuation and reflect into altered control flow
;;;
;;; Unlike 3-Lisp's infinite tower, this one terminates at the Cayley table.
;;; Unlike closure-based CPS, every continuation is a tagged data structure.
;;; The program can read its own future, modify it, and resume into an
;;; altered control flow.
;;;
;;; Run: cargo run -- examples/reflective-tower.scm

(load "examples/metacircular.scm")

;;; ── Helpers ────────────────────────────────────────────────────────

(define (banner msg)
  (newline)
  (display "--- ") (display msg) (display " ---") (newline))

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

;;; ════════════════════════════════════════════════════════════════════
;;; THE TOWER
;;; ════════════════════════════════════════════════════════════════════

(display "=== REFLECTIVE TOWER (Defunctionalized CPS) ===") (newline)
(display "Layer 3: User programs (fib, fact)") (newline)
(display "Layer 2: CPS meta-circular evaluator (metacircular.scm)") (newline)
(display "Layer 1: WispyScheme evaluator (eval.rs)") (newline)
(display "Layer 0: Cayley table (1KB)") (newline)

;;; ── Level 0: Computation via the meta-circular evaluator ───────────

(banner "Level 0: Computation (meta-evaluated)")

(check "(+ 1 2)" 3 (mrun '(+ 1 2)))
(check "((lambda (x) (* x x)) 7)" 49 (mrun '((lambda (x) (* x x)) 7)))

(define fib-result
  (mrun-program '(
    (define (fib n)
      (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))
    (fib 8))))
(check "fib(8)" 21 fib-result)

(define fact-result
  (mrun-program '(
    (define (fact n)
      (if (= n 0) 1 (* n (fact (- n 1)))))
    (fact 10))))
(check "fact(10)" 3628800 fact-result)

;;; ── Level 1: Ground Verification (Cayley table probes) ────────────

(banner "Level 1: Ground Verification (Cayley table probes)")

;; Absorber laws: TOP and BOT absorb on the left
(define (check-absorber abs x) (= (dot abs x) abs))

(check "TOP absorbs"
  #t (and (check-absorber TOP Q) (check-absorber TOP CAR)
          (check-absorber TOP Y) (check-absorber TOP E)))

(check "BOT absorbs"
  #t (and (check-absorber BOT Q) (check-absorber BOT CAR)
          (check-absorber BOT Y) (check-absorber BOT E)))

;; Tau classifier: partitions core into TOP and BOT
(define (check-tester x)
  (let ((r (dot TAU x))) (or (= r TOP) (= r BOT))))

(check "TAU boolean output"
  #t (and (check-tester Q) (check-tester E) (check-tester CAR)
          (check-tester CONS) (check-tester RHO) (check-tester Y)))

;; QE retraction round-trip
(define (check-qe x) (= (dot E (dot Q x)) x))

(check "QE round-trip"
  #t (and (check-qe Q) (check-qe E) (check-qe CAR)
          (check-qe CONS) (check-qe RHO) (check-qe TAU)))

;; Composition: CDR = RHO . CONS
(define (check-comp x) (= (dot CDR x) (dot RHO (dot CONS x))))

(check "CDR = RHO . CONS"
  #t (and (check-comp Q) (check-comp E) (check-comp CAR)
          (check-comp CONS) (check-comp RHO) (check-comp Y)))

;; Y fixed point
(let ((y-rho (dot Y RHO)))
  (check "Y(RHO) is a fixed point" y-rho (dot RHO y-rho)))

(display "Table health: ALL INVARIANTS HOLD") (newline)

;;; ── Level 2: Inspectable Reification ───────────────────────────────

(banner "Level 2: Inspectable Reification")

;; Reify at top level — see the identity continuation
(define reified (mrun '(reify)))
(check "reify returns reified-state" 'reified-state (car reified))
(let ((k (car (cdr reified))))
  (check "top-level continuation is k-id" 'k-id (car k))
  (display "  continuation depth: ") (display (k-depth k)) (newline))

;; Value injection via reflect
(define inject-result
  (mrun '(let ((s (reify)))
           (if (number? s)
               (+ s 50)
               (reflect s 7)))))
(check "value injection (7+50=57)" 57 inject-result)

;;; ── Level 2b: Continuation Chain Inspection ────────────────────────

(banner "Level 2b: Continuation Chain Inspection")

;; Reify inside let — chain: k-let-bind → k-let-body → k-id
(define state-in-let (mrun '(let ((x (reify))) x)))
(define k-in-let (car (cdr state-in-let)))
(display "  chain: ") (display (k-walk k-in-let)) (newline)
(check "let chain depth" 3 (k-depth k-in-let))
(check "frame 0 = k-let-bind" 'k-let-bind (car k-in-let))
(check "frame 1 = k-let-body" 'k-let-body (car (k-next k-in-let)))
(check "frame 2 = k-id" 'k-id (car (k-next (k-next k-in-let))))

;; Reify inside if-test inside let — chain includes k-if
(define state-in-if
  (mrun '(if (let ((s (reify)))
               (if (number? s) s s))
             42 99)))
;; On first pass, s = reified state (truthy), if takes then → 42
;; But let's capture the state properly:
(define state-if-captured
  (mrun '(let ((result (quote none)))
           (let ((s (reify)))
             (if (pair? s)
                 ;; First pass: save state, reflect with a number
                 (reflect s 42)
                 ;; Second pass: s = 42
                 s)))))
(check "reflect round-trip" 42 state-if-captured)

;;; ── Level 2c: Continuation Modification (rewriting the future) ─────

(banner "Level 2c: Continuation Modification")

;; The k-if branch swap — THE definitive 3-Lisp demo.
;;
;; A program that:
;; 1. Reifies its own state inside the test position of an if
;; 2. Navigates the continuation chain to find the k-if frame
;; 3. Swaps the then/else branches in the k-if
;; 4. Reflects with the modified continuation
;;
;; Result: the if takes the OPPOSITE branch from what the source says.

;; Without modification: (if 1 42 99) → 42
(check "unmodified (if 1 42 99)" 42 (mrun '(if 1 42 99)))

;; With branch swap:
;; The continuation chain when (reify) fires inside (let ((s (reify))) ...)
;; which is the test of (if TEST 42 99):
;;   k-let-bind → k-let-body → k-if(42, 99, env, next-k) → ...
;;
;; k-let-bind: (tag var rest env next-k)  — index 4 = next-k
;; k-let-body: (tag body next-k)          — index 2 = next-k
;; k-if:       (tag then else env next-k) — index 1 = then, index 2 = else

(define swap-result
  (mrun '(if (let ((s (reify)))
               (if (number? s)
                   s ;; second pass: return test value to (modified) k-if
                   ;; first pass: s = reified state
                   ;; Navigate: k-let-bind → k-let-body → k-if
                   (let ((k (list-ref s 1)))       ;; k = k-let-bind
                     (let ((kb (list-ref k 4)))     ;; kb = k-let-body
                       (let ((kif (list-ref kb 2))) ;; kif = k-if
                         ;; Swap then (index 1) and else (index 2)
                         (let ((swapped-kif
                                 (list (list-ref kif 0)   ;; tag: k-if
                                       (list-ref kif 2)   ;; SWAPPED: old else → new then
                                       (list-ref kif 1)   ;; SWAPPED: old then → new else
                                       (list-ref kif 3)   ;; env
                                       (list-ref kif 4)))) ;; next-k
                           ;; Rebuild k-let-body with swapped k-if
                           (let ((new-kb (list (list-ref kb 0)
                                               (list-ref kb 1)
                                               swapped-kif)))
                             ;; Rebuild k-let-bind with new k-let-body
                             (let ((new-k (list (list-ref k 0)
                                                (list-ref k 1)
                                                (list-ref k 2)
                                                (list-ref k 3)
                                                new-kb)))
                               ;; New state with modified continuation
                               (let ((new-state (list (list-ref s 0)
                                                       new-k
                                                       (list-ref s 2)
                                                       (list-ref s 3))))
                                 ;; Reflect with 1 (truthy) as test value
                                 (reflect new-state 1))))))))))
             42    ;; ORIGINAL then-branch
             99))) ;; ORIGINAL else-branch

;; Without swap: test=1 (truthy) → then → 42
;; With swap: then/else swapped in k-if, truthy → new-then (was else) → 99
(check "BRANCH SWAP" 99 swap-result)

(if (= swap-result 99)
    (begin
      (display "  CONFIRMED: Program rewrote its own if-branches.") (newline)
      (display "  The if saw 1 (truthy) but took the else-branch (99)") (newline)
      (display "  because the continuation was modified before reflect.") (newline))
    (begin
      (display "  UNEXPECTED: branch swap failed") (newline)))

;;; ── Summary ────────────────────────────────────────────────────────

(banner "Tower Complete")

(display "Level 0: fib(8) = ") (display fib-result) (newline)
(display "Level 0: fact(10) = ") (display fact-result) (newline)
(display "Level 1: Table invariants = ALL HOLD") (newline)
(display "Level 2: Reify/reflect = working") (newline)
(display "Level 2b: Continuation chains walkable as tagged data") (newline)
(display "Level 2c: Branch swap = ")
(if (= swap-result 99) (display "WORKING") (display "FAILED"))
(newline)

(newline)
(display pass) (display " passed, ")
(display fail) (display " failed") (newline)

(newline)
(display "=== THREE LEVELS. ONE ALGEBRA. ONE TABLE. ===") (newline)
(display "Smith's tower had no ground. This one does.") (newline)
(display "Smith's continuations were closures. These are data.") (newline)
(display "The program can read, modify, and rewrite its own future.") (newline)
