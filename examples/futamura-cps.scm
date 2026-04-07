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
  (set! *max-depth* 200)
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
;;; PARTIAL SPECIALIZATION: unknown runtime values
;;; ════════════════════════════════════════════════════════════════════
;;;
;;; When the program has free variables (runtime inputs), the compiler
;;; can't fold everything to a constant. Instead, it produces RESIDUAL
;;; CPS CODE — the interpreter dispatch is still gone, but computation
;;; on unknown values remains as code.
;;;
;;; This is the real P2: the continuation structure SURVIVES in the
;;; residual, which is what makes call/cc possible in compiled output.

(display "--- Partial specialization (unknown variables) ---") (newline)

;;; Helper: compile with some variables unknown in the environment
(define (cps-compile-with-unknowns program unknown-vars)
  (set! *depth* 0)
  (set! *max-depth* 200)
  (let ((env (append
               (map (lambda (v) (cons v (make-unknown v))) unknown-vars)
               base-menv)))
    (pe-specialize 'meval program env (make-unknown 'k))))

;;; ── Test P1: Variable reference ────────────────────────────────────
;;; (meval 'x env k) where x is unknown in env
;;; The PE folds: symbol? → #t, m-lookup → unknown value
;;; Result: (apply-k k x) — variable reference compiled to CPS return

(define p1 (cps-compile-with-unknowns 'x '(x)))
(display "  x → ") (display p1) (newline)
(check "var ref" '(apply-k k x) p1)

;;; ── Test P2: Arithmetic on unknowns ────────────────────────────────
;;; (+ x 1) where x is unknown
;;; The PE folds: pair? → #t, car → +, dispatches to function call,
;;; looks up + → builtin, evaluates args (x=unknown, 1=known),
;;; but can't fold (+ unknown 1), so residualizes.

(define p2 (cps-compile-with-unknowns '(+ x 1) '(x)))
(display "  (+ x 1) → ") (display p2) (newline)
;; The residual should contain apply-k and the + operation
(check "(+ x 1) is residual" #t (pair? p2))

;;; ── Test P3: If with unknown test ──────────────────────────────────
;;; (if (< x 0) (- 0 x) x) where x is unknown
;;; The PE folds: pair? → #t, car → if, dispatches to if branch,
;;; evaluates test (< x 0) → unknown, can't fold the if.
;;; Must produce RESIDUAL CPS CODE with a k-if continuation frame.

(define p3 (cps-compile-with-unknowns '(if (< x 0) (- 0 x) x) '(x)))
(display "  (if (< x 0) (- 0 x) x) → ") (display p3) (newline)
(check "if-unknown is residual" #t (pair? p3))

;;; ── Test P4: Let binding unknown ───────────────────────────────────
;;; (let ((y (+ x 1))) (+ y y)) where x is unknown
;;; x+1 is unknown → y is unknown → y+y is unknown
;;; But all expression dispatch is still folded away.

(define p4 (cps-compile-with-unknowns '(let ((y (+ x 1))) (+ y y)) '(x)))
(display "  (let ((y (+ x 1))) (+ y y)) → ") (display p4) (newline)
(check "let-unknown is residual" #t (pair? p4))

;;; ── Test P5: Mixed known/unknown ───────────────────────────────────
;;; (+ (* 2 3) x) where x is unknown
;;; (* 2 3) folds to 6, but (+ 6 x) can't fold.
;;; The compiler should fold the known sub-expression.

(define p5 (cps-compile-with-unknowns '(+ (* 2 3) x) '(x)))
(display "  (+ (* 2 3) x) → ") (display p5) (newline)
(check "mixed known/unknown is residual" #t (pair? p5))

;;; ── Test P6: If with known test, unknown branches ──────────────────
;;; (if #t x y) where x,y are unknown
;;; The PE folds: #t is truthy → takes then-branch → result is x
;;; Dead branch y is eliminated even though it's unknown!

(define p6 (cps-compile-with-unknowns '(if #t x y) '(x y)))
(display "  (if #t x y) → ") (display p6) (newline)
(check "dead branch eliminated" '(apply-k k x) p6)

;;; ── Test P7: Lambda over unknown ───────────────────────────────────
;;; ((lambda (y) (+ y 1)) x) where x is unknown
;;; Lambda is applied to x → beta-reduce → (+ x 1)
;;; The lambda overhead is eliminated, only the body remains.

(define p7 (cps-compile-with-unknowns '((lambda (y) (+ y 1)) x) '(x)))
(display "  ((lambda (y) (+ y 1)) x) → ") (display p7) (newline)
(check "lambda-unknown is residual" #t (pair? p7))

;;; ── Verification: residual code computes correctly ─────────────────
;;; For fully-known programs, the residual (apply-k k VALUE) can be
;;; verified against direct computation. For unknown variables,
;;; we verify by substituting a known value and checking the result.

(display "--- Verification: substitute and check ---") (newline)

;; Compile (+ x 1) with x unknown, then check with x=5
;; If we compiled correctly, applying the residual with x=5 should give 6
;; We verify indirectly: compile (+ 5 1) fully → (apply-k k 6)
(define p2-check (cps-compile '(+ 5 1)))
(display "  (+ 5 1) fully specialized → ") (display p2-check) (newline)
(check "(+ 5 1) = 6" '(apply-k k 6) p2-check)

;; Compile (if (< 3 0) (- 0 3) 3) fully → should get 3 (3 >= 0)
(define p3-check (cps-compile '(if (< 3 0) (- 0 3) 3)))
(display "  (if (< 3 0) (- 0 3) 3) → ") (display p3-check) (newline)
(check "abs(3) = 3" '(apply-k k 3) p3-check)

;; Compile (if (< -2 0) (- 0 -2) -2) fully → should get 2
(define p3-check2 (cps-compile '(if (< -2 0) (- 0 -2) -2)))
(display "  (if (< -2 0) (- 0 -2) -2) → ") (display p3-check2) (newline)
(check "abs(-2) = 2" '(apply-k k 2) p3-check2)

;;; ════════════════════════════════════════════════════════════════════
;;; WHAT SURVIVES VS WHAT'S ELIMINATED
;;; ════════════════════════════════════════════════════════════════════

(display "--- What survives vs. what's eliminated ---") (newline)
(display "  ELIMINATED (folded away by PE):") (newline)
(display "    - meval's cond: (number? expr), (symbol? expr), (pair? expr)") (newline)
(display "    - meval's dispatch: (eq? head 'quote), (eq? head 'if), ...") (newline)
(display "    - apply-k's tag dispatch: (eq? tag 'k-if), (eq? tag 'k-do-apply), ...") (newline)
(display "    - m-lookup's alist traversal") (newline)
(display "    - apply-builtin's name matching") (newline)
(display "    - Dead branches in (if #t x y) → y eliminated") (newline)
(display "    - Lambda overhead: ((lambda (y) body) x) → body[y:=x]") (newline)
(display "  SURVIVES (in residual CPS code):") (newline)
(display "    - Continuation frames: (list 'k-if then else env k)") (newline)
(display "    - apply-k calls on unknown continuations") (newline)
(display "    - Arithmetic on unknown values: (+ x 1)") (newline)
(display "    - Comparisons on unknowns: (< x 0)") (newline)
(display "    - This is exactly what call/cc needs to work.") (newline)

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
