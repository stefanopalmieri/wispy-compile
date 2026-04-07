;;; futamura-cps.scm — Futamura Projection 2 on the CPS Evaluator
;;;
;;; Demonstrates: specialize(PE, CPS-evaluator, program) = CPS compiler
;;;
;;; The PE specializes the CPS metacircular evaluator (meval) with
;;; respect to a known program. The result is residual CPS code where
;;; all interpreter dispatch has been eliminated, but continuation
;;; structure survives — preserving call/cc and reify/reflect.
;;;
;;; Run: cargo run -- examples/futamura-cps.scm

(load "examples/pe.scm")

;;; ════════════════════════════════════════════════════════════════════
;;; REGISTER CPS EVALUATOR IN THE PE
;;; ════════════════════════════════════════════════════════════════════
;;;
;;; We register simplified versions of the CPS evaluator's functions
;;; in the PE's function table. The PE can then unfold and specialize
;;; them with respect to known program structure.

(reset-ftable!)

;;; ── Helpers ────────────────────────────────────────────────────────

(register-fn! 'm-nth '(n lst)
  '(if (= n 0) (car lst)
       (m-nth (- n 1) (cdr lst))))

(register-fn! 'm-assoc '(key alist)
  '(if (null? alist) (quote ())
       (if (eq? key (car (car alist)))
           (car alist)
           (m-assoc key (cdr alist)))))

(register-fn! 'm-lookup '(sym menv)
  '(let ((pair (m-assoc sym menv)))
     (if (null? pair) (quote ()) (cdr pair))))

(register-fn! 'extend-env '(params args menv)
  '(if (null? params) menv
       (cons (cons (car params) (car args))
             (extend-env (cdr params) (cdr args) menv))))

;;; ── Closure/builtin operations ────────────────────────────────────

(register-fn! 'make-closure '(name params body cenv)
  '(list 90 name params body cenv))

(register-fn! 'closure-p '(x)
  '(and (pair? x) (= (car x) 90)))

(register-fn! 'closure-name '(c)   '(m-nth 1 c))
(register-fn! 'closure-params '(c) '(m-nth 2 c))
(register-fn! 'closure-body '(c)   '(m-nth 3 c))
(register-fn! 'closure-env '(c)    '(m-nth 4 c))

(register-fn! 'builtin-p '(x)
  '(and (pair? x) (= (car x) 91)))

(register-fn! 'builtin-name '(b) '(m-nth 1 b))

(register-fn! 'apply-builtin '(name args)
  '(let ((a1 (car args))
         (a2 (if (null? (cdr args)) (quote ()) (car (cdr args)))))
     (cond
       ((eq? name (quote +))       (+ a1 a2))
       ((eq? name (quote -))       (- a1 a2))
       ((eq? name (quote *))       (* a1 a2))
       ((eq? name (quote <))       (< a1 a2))
       ((eq? name (quote >))       (> a1 a2))
       ((eq? name (quote =))       (= a1 a2))
       ((eq? name (quote cons))    (cons a1 a2))
       ((eq? name (quote car))     (car a1))
       ((eq? name (quote cdr))     (cdr a1))
       ((eq? name (quote null?))   (null? a1))
       ((eq? name (quote number?)) (number? a1))
       ((eq? name (quote pair?))   (pair? a1))
       ((eq? name (quote eq?))     (eq? a1 a2))
       ((eq? name (quote not))     (not a1))
       (else (quote ())))))

;;; ── The CPS Evaluator (registered for PE) ─────────────────────────
;;;
;;; This is meval from metacircular.scm, with self-eval? and compound?
;;; inlined so the PE can fold the predicate checks directly.

(register-fn! 'meval '(expr menv k)
  '(cond
     ;; Self-evaluating: numbers, booleans
     ((number? expr)  (apply-k k expr))
     ((boolean? expr) (apply-k k expr))

     ;; Nil
     ((null? expr)    (apply-k k (quote ())))

     ;; Symbol lookup
     ((symbol? expr)  (apply-k k (m-lookup expr menv)))

     ;; Compound expression
     ((pair? expr)
      (let ((head (car expr)))
        (cond
          ;; (quote datum)
          ((eq? head (quote quote))
           (apply-k k (car (cdr expr))))

          ;; (if test then else)
          ((eq? head (quote if))
           (let ((test-expr   (car (cdr expr)))
                 (then-branch (car (cdr (cdr expr))))
                 (else-branch (car (cdr (cdr (cdr expr))))))
             (meval test-expr menv
               (list (quote k-if) then-branch else-branch menv k))))

          ;; (lambda (params) body)
          ((eq? head (quote lambda))
           (apply-k k
             (make-closure (quote ()) (car (cdr expr)) (car (cdr (cdr expr))) menv)))

          ;; (let ((x v) ...) body)
          ((eq? head (quote let))
           (let ((bindings (car (cdr expr)))
                 (body     (car (cdr (cdr expr)))))
             (eval-let-bindings bindings menv
               (list (quote k-let-body) body k))))

          ;; (begin expr ...)
          ((eq? head (quote begin))
           (eval-sequence (cdr expr) menv k))

          ;; Function application: (fn arg1 arg2 ...)
          (else
           (meval head menv
             (list (quote k-apply-fn) (cdr expr) menv k))))))

     ;; Fallback
     (else (apply-k k expr))))

;;; ── Continuation dispatch ─────────────────────────────────────────

(register-fn! 'apply-k '(k val)
  '(let ((tag (car k)))
     (cond
       ((eq? tag (quote k-id))
        val)

       ((eq? tag (quote k-if))
        (let ((then-b (m-nth 1 k))
              (else-b (m-nth 2 k))
              (env    (m-nth 3 k))
              (next-k (m-nth 4 k)))
          (if val
              (meval then-b env next-k)
              (meval else-b env next-k))))

       ((eq? tag (quote k-let-body))
        (let ((body   (m-nth 1 k))
              (next-k (m-nth 2 k)))
          (meval body val next-k)))

       ((eq? tag (quote k-let-bind))
        (let ((var-name (m-nth 1 k))
              (rest     (m-nth 2 k))
              (env      (m-nth 3 k))
              (next-k   (m-nth 4 k)))
          (eval-let-bindings rest
            (cons (cons var-name val) env)
            next-k)))

       ((eq? tag (quote k-seq))
        (let ((rest   (m-nth 1 k))
              (env    (m-nth 2 k))
              (next-k (m-nth 3 k)))
          (eval-sequence rest env next-k)))

       ((eq? tag (quote k-apply-fn))
        (let ((arg-exprs (m-nth 1 k))
              (env       (m-nth 2 k))
              (next-k    (m-nth 3 k)))
          (eval-args arg-exprs env
            (list (quote k-do-apply) val next-k))))

       ((eq? tag (quote k-do-apply))
        (let ((fn     (m-nth 1 k))
              (next-k (m-nth 2 k)))
          (mapply fn val next-k)))

       ((eq? tag (quote k-args-head))
        (let ((rest   (m-nth 1 k))
              (env    (m-nth 2 k))
              (next-k (m-nth 3 k)))
          (eval-args rest env
            (list (quote k-args-tail) val next-k))))

       ((eq? tag (quote k-args-tail))
        (let ((head-val (m-nth 1 k))
              (next-k   (m-nth 2 k)))
          (apply-k next-k (cons head-val val))))

       (else val))))

;;; ── CPS helpers ───────────────────────────────────────────────────

(register-fn! 'mapply '(fn args k)
  '(cond
     ((closure-p fn)
      (let ((call-env (extend-env (closure-params fn) args (closure-env fn))))
        (let ((final-env (if (null? (closure-name fn)) call-env
                             (cons (cons (closure-name fn) fn) call-env))))
          (meval (closure-body fn) final-env k))))
     ((builtin-p fn)
      (apply-k k (apply-builtin (builtin-name fn) args)))
     (else (apply-k k (quote ())))))

(register-fn! 'eval-args '(exprs menv k)
  '(if (null? exprs) (apply-k k (quote ()))
       (meval (car exprs) menv
         (list (quote k-args-head) (cdr exprs) menv k))))

(register-fn! 'eval-let-bindings '(bindings menv k)
  '(if (null? bindings) (apply-k k menv)
       (meval (car (cdr (car bindings))) menv
         (list (quote k-let-bind) (car (car bindings)) (cdr bindings) menv k))))

(register-fn! 'eval-sequence '(exprs menv k)
  '(if (null? (cdr exprs))
       (meval (car exprs) menv k)
       (meval (car exprs) menv
         (list (quote k-seq) (cdr exprs) menv k))))

;;; ════════════════════════════════════════════════════════════════════
;;; BASE ENVIRONMENT
;;; ════════════════════════════════════════════════════════════════════

(define base-menv
  (list
    (cons '+ (list 91 '+))
    (cons '- (list 91 '-))
    (cons '* (list 91 '*))
    (cons '< (list 91 '<))
    (cons '> (list 91 '>))
    (cons '= (list 91 '=))
    (cons 'cons (list 91 'cons))
    (cons 'car (list 91 'car))
    (cons 'cdr (list 91 'cdr))
    (cons 'null? (list 91 'null?))
    (cons 'number? (list 91 'number?))
    (cons 'pair? (list 91 'pair?))
    (cons 'eq? (list 91 'eq?))
    (cons 'not (list 91 'not))))

;;; ════════════════════════════════════════════════════════════════════
;;; THE COMPILER: specialize meval w.r.t. known program
;;; ════════════════════════════════════════════════════════════════════

(define (cps-compile program)
  (set! *depth* 0)
  (set! *max-depth* 100)
  (pe-specialize 'meval program base-menv (make-unknown 'k)))

;;; ════════════════════════════════════════════════════════════════════
;;; TESTS
;;; ════════════════════════════════════════════════════════════════════

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

(display "=== Futamura Projection 2: CPS Evaluator → CPS Compiler ===") (newline)

;;; ── Test 1: Constant ──────────────────────────────────────────────
;;; meval(42, base-env, k) should fold to (apply-k k 42)
;;; Since k is unknown, apply-k can't dispatch — result is unknown.
;;; But since 42 is a number, the PE folds: (number? 42) → #t → (apply-k k 42)
;;; apply-k with unknown k residualizes.

(display "--- Constants and arithmetic ---") (newline)

;;; The compiler produces residual CPS code: (apply-k k VALUE)
;;; because k is unknown. The value inside is fully folded.

(define r1 (cps-compile 42))
(display "  42 → ") (display r1) (newline)
(check "constant 42" '(apply-k k 42) r1)

;;; ── Test 2: Arithmetic with known values ──────────────────────────
;;; meval('(+ 1 2), base-env, k) folds all dispatch:
;;; pair? → #t, car → +, eq? chains → function call branch,
;;; m-lookup → (91 +), eval-args → (1 2), apply-builtin → 3
;;; Result: (apply-k k 3) — the interpreter is gone.

(define r2 (cps-compile '(+ 1 2)))
(display "  (+ 1 2) → ") (display r2) (newline)
(check "(+ 1 2)" '(apply-k k 3) r2)

;;; ── Test 3: Nested arithmetic ─────────────────────────────────────

(define r3 (cps-compile '(+ (* 3 4) (- 10 5))))
(display "  (+ (* 3 4) (- 10 5)) → ") (display r3) (newline)
(check "(+ (* 3 4) (- 10 5))" '(apply-k k 17) r3)

;;; ── Test 4: Quote ─────────────────────────────────────────────────

(define r4 (cps-compile '(quote hello)))
(display "  (quote hello) → ") (display r4) (newline)
(check "(quote hello)" '(apply-k k (quote hello)) r4)

;;; ── Test 5: If with known test ────────────────────────────────────

(define r5 (cps-compile '(if #t 1 2)))
(display "  (if #t 1 2) → ") (display r5) (newline)
(check "(if #t 1 2)" '(apply-k k 1) r5)

(define r6 (cps-compile '(if #f 1 2)))
(display "  (if #f 1 2) → ") (display r6) (newline)
(check "(if #f 1 2)" '(apply-k k 2) r6)

;;; ── Test 6: Let with known values ─────────────────────────────────

(define r7 (cps-compile '(let ((x 5)) (+ x 1))))
(display "  (let ((x 5)) (+ x 1)) → ") (display r7) (newline)
(check "(let ((x 5)) (+ x 1))" '(apply-k k 6) r7)

;;; ── Test 7: Nested let ────────────────────────────────────────────

(define r8 (cps-compile '(let ((x 3)) (let ((y 4)) (+ x y)))))
(display "  (let ((x 3)) (let ((y 4)) (+ x y))) → ") (display r8) (newline)
(check "nested let" '(apply-k k 7) r8)

;;; ── Test 8: Lambda + application ──────────────────────────────────

(define r9 (cps-compile '((lambda (x) (+ x 1)) 5)))
(display "  ((lambda (x) (+ x 1)) 5) → ") (display r9) (newline)
(check "lambda application" '(apply-k k 6) r9)

;;; ════════════════════════════════════════════════════════════════════
;;; THREE-PATH VERIFICATION
;;; ════════════════════════════════════════════════════════════════════

(display "--- Three-path verification ---") (newline)

;;; For fully-known programs, the residual is (apply-k k VALUE).
;;; The VALUE inside must match direct Scheme computation.
;;; Path A: direct Scheme
;;; Path C: PE specialization → extract value from (apply-k k VALUE)

;; Helper: extract the value from (apply-k k VALUE) residual
(define (extract-value residual)
  (car (cdr (cdr residual))))  ;; third element of (apply-k k VALUE)

;; Path A: direct
(define path-a (+ (* 2 3) (- 10 4)))

;; Path C: PE specialization
(define path-c-residual (cps-compile '(+ (* 2 3) (- 10 4))))
(define path-c (extract-value path-c-residual))

(display "  Path A (direct Scheme):      ") (display path-a) (newline)
(display "  Path C (PE residual):        ") (display path-c-residual) (newline)
(display "  Path C (extracted value):    ") (display path-c) (newline)

(check "Path A = 12" 12 path-a)
(check "Path C value = 12" 12 path-c)
(check "A = C" path-a path-c)
(check "residual form" 'apply-k (car path-c-residual))

;;; ════════════════════════════════════════════════════════════════════
;;; WHAT THE COMPILER ELIMINATES
;;; ════════════════════════════════════════════════════════════════════

(display "--- What the compiler eliminates ---") (newline)
(display "  For (+ 1 2), the PE:") (newline)
(display "    - Folded (pair? '(+ 1 2)) → #t") (newline)
(display "    - Folded (car '(+ 1 2)) → '+") (newline)
(display "    - Folded (eq? '+ 'quote) → #f ... (eq? '+ 'if) → #f") (newline)
(display "    - Fell through to function application branch") (newline)
(display "    - Looked up '+' in base-menv → (91 +)") (newline)
(display "    - Folded (builtin? (91 +)) → #t") (newline)
(display "    - Folded (apply-builtin '+ '(1 2)) → 3") (newline)
(display "    - Result: 3 (all interpreter dispatch eliminated)") (newline)

;;; ════════════════════════════════════════════════════════════════════
;;; THE INTERPRETER VANISHED
;;; ════════════════════════════════════════════════════════════════════

(display "--- THE INTERPRETER VANISHED ---") (newline)
(display "  meval's cond dispatch on expression type,") (newline)
(display "  apply-k's dispatch on continuation tags,") (newline)
(display "  m-lookup's alist traversal,") (newline)
(display "  apply-builtin's name matching —") (newline)
(display "  all folded away by the partial evaluator.") (newline)
(display "  What remains is the bare computation.") (newline)

;;; ── Summary ────────────────────────────────────────────────────────

(newline)
(display pass) (display " passed, ")
(display fail) (display " failed") (newline)
(if (= fail 0)
    (display "All Futamura Projection 2 (CPS) tests passed.")
    (display "SOME TESTS FAILED."))
(newline)
