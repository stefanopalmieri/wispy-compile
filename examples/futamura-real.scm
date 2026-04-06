;;; futamura-real.scm — Futamura Projection 1 on a Real Scheme Evaluator
;;;
;;; Demonstrates: specialize(interpreter, program) = compiled program
;;; The interpreter vanishes. Only the computation remains.
;;;
;;; Run: cargo run -- examples/futamura-real.scm

(load "examples/pe.scm")

;;; ════════════════════════════════════════════════════════════════════
;;; THE DIRECT-STYLE EVALUATOR
;;; ════════════════════════════════════════════════════════════════════
;;;
;;; A minimal Scheme interpreter: numbers, symbols, if, arithmetic,
;;; comparison, and named function calls with recursion.
;;;
;;; This is what we'll specialize away.

(define (deval-lookup sym env)
  (if (null? env) 0
      (if (eq? sym (car (car env)))
          (cdr (car env))
          (deval-lookup sym (cdr env)))))

(define (deval expr env fns)
  (cond
    ((number? expr) expr)
    ((boolean? expr) expr)
    ((symbol? expr) (deval-lookup expr env))
    ((eq? (car expr) 'if)
     (if (deval (car (cdr expr)) env fns)
         (deval (car (cdr (cdr expr))) env fns)
         (deval (car (cdr (cdr (cdr expr)))) env fns)))
    ((eq? (car expr) '+)
     (+ (deval (car (cdr expr)) env fns)
        (deval (car (cdr (cdr expr))) env fns)))
    ((eq? (car expr) '-)
     (- (deval (car (cdr expr)) env fns)
        (deval (car (cdr (cdr expr))) env fns)))
    ((eq? (car expr) '*)
     (* (deval (car (cdr expr)) env fns)
        (deval (car (cdr (cdr expr))) env fns)))
    ((eq? (car expr) '<)
     (< (deval (car (cdr expr)) env fns)
        (deval (car (cdr (cdr expr))) env fns)))
    ((eq? (car expr) '=)
     (= (deval (car (cdr expr)) env fns)
        (deval (car (cdr (cdr expr))) env fns)))
    (else
     ;; Function call: (fname arg) — single argument for simplicity
     (let ((fn-entry (deval-lookup (car expr) fns)))
       (let ((params (car fn-entry))
             (body (cdr fn-entry)))
         (deval body
                (cons (cons (car params)
                            (deval (car (cdr expr)) env fns))
                      env)
                fns))))))

;;; ── Test deval directly ────────────────────────────────────────────

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

(display "=== Futamura Projection 1: Real Evaluator ===") (newline)
(display "--- Direct evaluation (deval) ---") (newline)

;; Function table: name → (params . body)
(define fib-fns
  (list (cons 'fib (cons '(n) '(if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))))))

(define fact-fns
  (list (cons 'fact (cons '(n) '(if (= n 0) 1 (* n (fact (- n 1))))))))

(check "deval (+ 1 2)" 3 (deval '(+ 1 2) '() '()))
(check "deval (if #t 1 2)" 1 (deval '(if #t 1 2) '() '()))
(check "deval (if #f 1 2)" 2 (deval '(if #f 1 2) '() '()))
(check "deval fib(8)" 21 (deval '(fib 8) '() fib-fns))
(check "deval fact(5)" 120 (deval '(fact 5) '() fact-fns))

;;; ════════════════════════════════════════════════════════════════════
;;; FUTAMURA PROJECTION 1
;;; ════════════════════════════════════════════════════════════════════
;;;
;;; Register deval and its helpers in the PE function table.
;;; Specialize with known program (fib source) and known input (n=8).
;;; The PE should unfold all deval dispatch and fold all computation.

(display "--- Registering deval in PE ---") (newline)

(reset-ftable!)

(register-fn! 'deval-lookup '(sym env)
  '(if (null? env) 0
       (if (eq? sym (car (car env)))
           (cdr (car env))
           (deval-lookup sym (cdr env)))))

(register-fn! 'deval '(expr env fns)
  '(cond
     ((number? expr) expr)
     ((boolean? expr) expr)
     ((symbol? expr) (deval-lookup expr env))
     ((eq? (car expr) (quote if))
      (if (deval (car (cdr expr)) env fns)
          (deval (car (cdr (cdr expr))) env fns)
          (deval (car (cdr (cdr (cdr expr)))) env fns)))
     ((eq? (car expr) (quote +))
      (+ (deval (car (cdr expr)) env fns)
         (deval (car (cdr (cdr expr))) env fns)))
     ((eq? (car expr) (quote -))
      (- (deval (car (cdr expr)) env fns)
         (deval (car (cdr (cdr expr))) env fns)))
     ((eq? (car expr) (quote *))
      (* (deval (car (cdr expr)) env fns)
         (deval (car (cdr (cdr expr))) env fns)))
     ((eq? (car expr) (quote <))
      (< (deval (car (cdr expr)) env fns)
         (deval (car (cdr (cdr expr))) env fns)))
     ((eq? (car expr) (quote =))
      (= (deval (car (cdr expr)) env fns)
         (deval (car (cdr (cdr expr))) env fns)))
     (else
      (let ((fn-entry (deval-lookup (car expr) fns)))
        (let ((params (car fn-entry))
              (body (cdr fn-entry)))
          (deval body
                 (cons (cons (car params) (deval (car (cdr expr)) env fns)) env)
                 fns))))))

;;; ── Path C: Fully specialize deval(fib(8)) ─────────────────────────

(display "--- Specializing deval(fib, n=8) ---") (newline)

(define fib-program '(fib 8))
(define fib-fns-data
  (list (cons 'fib (cons '(n) '(if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))))))

(define path-c
  (pe-specialize 'deval fib-program '() fib-fns-data))

(display "  PE result: ") (display path-c) (newline)

;;; ── Four-path verification ─────────────────────────────────────────

(display "--- FOUR-PATH VERIFICATION ---") (newline)

;; Path A: direct Scheme
(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))
(define path-a (fib 8))

;; Path B: through deval
(define path-b (deval '(fib 8) '() fib-fns))

;; Path C: PE specialization of deval (already computed above)

(display "  Path A (direct Scheme):     ") (display path-a) (newline)
(display "  Path B (deval interpreter):  ") (display path-b) (newline)
(display "  Path C (PE specialized):     ") (display path-c) (newline)

(check "Path A = 21" 21 path-a)
(check "Path B = 21" 21 path-b)
(check "Path C = 21" 21 path-c)
(check "A = B" path-a path-b)
(check "B = C" path-b path-c)

(display "--- THE INTERPRETER VANISHED ---") (newline)
(display "  deval's cond dispatch, symbol lookup, car/cdr traversal —") (newline)
(display "  all folded away by the partial evaluator.") (newline)
(display "  What remains is the bare computation: 21.") (newline)

;;; ── Summary ────────────────────────────────────────────────────────

(newline)
(display pass) (display " passed, ")
(display fail) (display " failed") (newline)
(if (= fail 0)
    (display "All Futamura Projection 1 tests passed.")
    (display "SOME TESTS FAILED."))
(newline)
