;;; metacircular.scm — Defunctionalized CPS Meta-Circular Evaluator
;;;
;;; Ported from Kamea's psi_metacircular.lisp to WispyScheme Scheme.
;;;
;;; A Scheme interpreter written in Scheme with INSPECTABLE continuations.
;;; Follows Smith's 3-Lisp (1984), Reynolds' definitional interpreters (1972),
;;; and Danvy & Nielsen's defunctionalization at work (2001).
;;;
;;; Every continuation is a tagged data structure — a list with a tag
;;; symbol and captured values. No lambdas in the evaluator's control flow.
;;; (reify) returns a fully inspectable state: the program can walk the
;;; continuation chain, see what computation is pending, modify it,
;;; and reflect into an altered future.
;;;
;;; Architecture:
;;;   Layer 3: User program (e.g., fib 8)
;;;            ↓ interpreted by
;;;   Layer 2: This CPS evaluator (metacircular.scm)
;;;            ↓ interpreted by
;;;   Layer 1: WispyScheme evaluator (eval.rs)
;;;            ↓ executes via
;;;   Layer 0: Cayley table (1KB)
;;;
;;; Run: cargo run -- examples/metacircular.scm

;;; ── Tags for meta-level values ─────────────────────────────────────

(define CLOSURE-TAG 90)
(define BUILTIN-TAG 91)

;;; ── List access helper ─────────────────────────────────────────────

(define (m-nth n lst)
  (if (= n 0) (car lst)
      (m-nth (- n 1) (cdr lst))))

;;; ── Association list operations ────────────────────────────────────

(define (m-assoc key alist)
  (if (null? alist) '()
      (if (eq? key (car (car alist)))
          (car alist)
          (m-assoc key (cdr alist)))))

(define (m-lookup sym menv)
  (let ((pair (m-assoc sym menv)))
    (if (null? pair) '() (cdr pair))))

(define (extend-env params args menv)
  (if (null? params) menv
      (cons (cons (car params) (car args))
            (extend-env (cdr params) (cdr args) menv))))

;;; ── Closure constructors/accessors ─────────────────────────────────

(define (make-closure name params body cenv)
  (list CLOSURE-TAG name params body cenv))

(define (closure? x)
  (and (pair? x) (= (car x) CLOSURE-TAG)))

(define (closure-name c)   (m-nth 1 c))
(define (closure-params c) (m-nth 2 c))
(define (closure-body c)   (m-nth 3 c))
(define (closure-env c)    (m-nth 4 c))

;;; ── Builtin constructors/accessors ─────────────────────────────────

(define (make-builtin name) (list BUILTIN-TAG name))

(define (builtin? x)
  (and (pair? x) (= (car x) BUILTIN-TAG)))

(define (builtin-name b) (m-nth 1 b))

;;; ── Builtin dispatch ───────────────────────────────────────────────

(define (apply-builtin name args)
  (let ((a1 (car args))
        (a2 (if (null? (cdr args)) '() (car (cdr args)))))
    (cond
      ((eq? name '+)       (+ a1 a2))
      ((eq? name '-)       (- a1 a2))
      ((eq? name '*)       (* a1 a2))
      ((eq? name '<)       (if (< a1 a2) #t #f))
      ((eq? name '>)       (if (> a1 a2) #t #f))
      ((eq? name '=)       (if (= a1 a2) #t #f))
      ((eq? name 'cons)    (cons a1 a2))
      ((eq? name 'car)     (car a1))
      ((eq? name 'cdr)     (cdr a1))
      ((eq? name 'null?)   (if (null? a1) #t #f))
      ((eq? name 'number?) (if (number? a1) #t #f))
      ((eq? name 'pair?)   (if (pair? a1) #t #f))
      ((eq? name 'eq?)     (if (eq? a1 a2) #t #f))
      ((eq? name 'not)     (if (eq? a1 #f) #t #f))
      ((eq? name 'display) (begin (display a1) a1))
      ((eq? name 'newline) (begin (newline) '()))
      ((eq? name 'list)    args)
      ((eq? name 'list-ref) (m-nth a2 a1))
      (else '()))))

;;; ── Expression predicates ──────────────────────────────────────────

(define (self-eval? expr)
  (or (number? expr)
      (string? expr)
      (boolean? expr)
      (char? expr)))

(define (compound? expr)
  (pair? expr))

;;; ── Continuation Dispatch ──────────────────────────────────────────
;;; Every continuation is a tagged list. apply-k dispatches on the tag.

(define (apply-k k val)
  (let ((tag (car k)))
    (cond
      ;; k-id: identity continuation (top of chain)
      ((eq? tag 'k-id)
       val)

      ;; k-if: if-test just evaluated
      ;; (k-if then-branch else-branch env next-k)
      ;; Use host's `if` for falsity check (tag-based, not pointer eq)
      ((eq? tag 'k-if)
       (let ((then-b (m-nth 1 k))
             (else-b (m-nth 2 k))
             (env    (m-nth 3 k))
             (next-k (m-nth 4 k)))
         (if val
             (meval then-b env next-k)
             (if (null? else-b)
                 (apply-k next-k '())
                 (meval else-b env next-k)))))

      ;; k-cond: cond clause test just evaluated
      ;; (k-cond rest-clauses consequent env next-k)
      ;; Use host's `if` for falsity check
      ((eq? tag 'k-cond)
       (let ((rest       (m-nth 1 k))
             (consequent (m-nth 2 k))
             (env        (m-nth 3 k))
             (next-k     (m-nth 4 k)))
         (if val
             (meval consequent env next-k)
             (eval-cond rest env next-k))))

      ;; k-let-body: all let-bindings done, evaluate body
      ;; val = the extended environment
      ((eq? tag 'k-let-body)
       (let ((body   (m-nth 1 k))
             (next-k (m-nth 2 k)))
         (meval body val next-k)))

      ;; k-let-bind: one let-binding just evaluated
      ;; (k-let-bind var-name rest-bindings env next-k)
      ((eq? tag 'k-let-bind)
       (let ((var-name (m-nth 1 k))
             (rest     (m-nth 2 k))
             (env      (m-nth 3 k))
             (next-k   (m-nth 4 k)))
         (eval-let-bindings rest
           (cons (cons var-name val) env)
           next-k)))

      ;; k-seq: sequence element just evaluated
      ;; (k-seq rest-exprs env next-k)
      ((eq? tag 'k-seq)
       (let ((rest   (m-nth 1 k))
             (env    (m-nth 2 k))
             (next-k (m-nth 3 k)))
         (eval-sequence rest env next-k)))

      ;; k-apply-fn: function position just evaluated
      ;; (k-apply-fn arg-exprs env next-k)
      ((eq? tag 'k-apply-fn)
       (let ((arg-exprs (m-nth 1 k))
             (env       (m-nth 2 k))
             (next-k    (m-nth 3 k)))
         (eval-args arg-exprs env
           (list 'k-do-apply val next-k))))

      ;; k-do-apply: all arguments evaluated, apply function
      ;; (k-do-apply fn next-k)
      ((eq? tag 'k-do-apply)
       (let ((fn     (m-nth 1 k))
             (next-k (m-nth 2 k)))
         (mapply fn val next-k)))

      ;; k-args-head: first arg just evaluated
      ;; (k-args-head rest-exprs env next-k)
      ((eq? tag 'k-args-head)
       (let ((rest   (m-nth 1 k))
             (env    (m-nth 2 k))
             (next-k (m-nth 3 k)))
         (eval-args rest env
           (list 'k-args-tail val next-k))))

      ;; k-args-tail: remaining args just evaluated
      ;; (k-args-tail head-val next-k)
      ((eq? tag 'k-args-tail)
       (let ((head-val (m-nth 1 k))
             (next-k   (m-nth 2 k)))
         (apply-k next-k (cons head-val val))))

      ;; k-reflect-state: reflect state expression evaluated
      ;; (k-reflect-state value-expr env)
      ((eq? tag 'k-reflect-state)
       (let ((value-expr (m-nth 1 k))
             (env        (m-nth 2 k)))
         (meval value-expr env
           (list 'k-reflect-jump val))))

      ;; k-reflect-jump: reflect value evaluated, jump
      ;; (k-reflect-jump state)
      ((eq? tag 'k-reflect-jump)
       (let ((state (m-nth 1 k)))
         (let ((saved-k (car (cdr state))))
           (apply-k saved-k val))))

      ;; k-define: define just evaluated
      ;; (k-define name env next-k)
      ((eq? tag 'k-define)
       (let ((name   (m-nth 1 k))
             (env    (m-nth 2 k))
             (next-k (m-nth 3 k)))
         (apply-k-top next-k val
           (cons (cons name val) env))))

      ;; Fallback
      (else val))))

;;; ── Toplevel Continuation Dispatch ─────────────────────────────────

(define (apply-k-top k val env)
  (let ((tag (car k)))
    (cond
      ((eq? tag 'k-top-id)
       val)

      ;; k-program-step: continue with remaining top-level forms
      ;; (k-program-step rest-exprs final-k)
      ((eq? tag 'k-program-step)
       (let ((rest    (m-nth 1 k))
             (final-k (m-nth 2 k)))
         (if (null? rest)
             (apply-k final-k val)
             (meval-program rest env final-k))))

      (else val))))

;;; ── The CPS Evaluator ─────────────────────────────────────────────

(define (meval expr menv k)
  (cond
    ;; Self-evaluating: numbers, strings, booleans, chars
    ((self-eval? expr)  (apply-k k expr))

    ;; Nil
    ((null? expr)       (apply-k k '()))

    ;; Symbol lookup
    ((symbol? expr)     (apply-k k (m-lookup expr menv)))

    ;; Compound expression
    ((compound? expr)
     (let ((head (car expr)))
       (cond
         ;; (quote datum)
         ((eq? head 'quote)
          (apply-k k (car (cdr expr))))

         ;; (if test then else)
         ((eq? head 'if)
          (let ((test-expr  (car (cdr expr)))
                (then-branch (car (cdr (cdr expr))))
                (else-part   (cdr (cdr (cdr expr)))))
            (let ((else-branch (if (null? else-part) '() (car else-part))))
              (meval test-expr menv
                (list 'k-if then-branch else-branch menv k)))))

         ;; (cond (test expr) ...)
         ((eq? head 'cond)
          (eval-cond (cdr expr) menv k))

         ;; (lambda (params) body)
         ((eq? head 'lambda)
          (apply-k k (make-closure '() (car (cdr expr)) (car (cdr (cdr expr))) menv)))

         ;; (let ((x v) ...) body ...) — multi-body wrapped in begin
         ((eq? head 'let)
          (let ((bindings (car (cdr expr)))
                (body-exprs (cdr (cdr expr))))
            (let ((body (if (null? (cdr body-exprs))
                            (car body-exprs)
                            (cons 'begin body-exprs))))
              (eval-let-bindings bindings menv
                (list 'k-let-body body k)))))

         ;; (begin expr ...)
         ((eq? head 'begin)
          (eval-sequence (cdr expr) menv k))

         ;; (define name value) — top-level binding
         ((eq? head 'define)
          (let ((name (car (cdr expr)))
                (val-expr (car (cdr (cdr expr)))))
            (meval val-expr menv
              (list 'k-define name menv k))))

         ;; (reify) — capture current continuation and environment
         ((eq? head 'reify)
          (apply-k k (list 'reified-state k menv expr)))

         ;; (reflect state value) — jump to saved continuation
         ((eq? head 'reflect)
          (meval (car (cdr expr)) menv
            (list 'k-reflect-state (car (cdr (cdr expr))) menv)))

         ;; Function application: (fn arg1 arg2 ...)
         (else
          (meval head menv
            (list 'k-apply-fn (cdr expr) menv k))))))

    ;; Fallback
    (else (apply-k k expr))))

;;; ── CPS helpers ────────────────────────────────────────────────────

(define (mapply fn args k)
  (cond
    ((closure? fn)
     (let ((call-env (extend-env (closure-params fn) args (closure-env fn))))
       ;; If named, bind self for recursion
       (let ((final-env (if (null? (closure-name fn)) call-env
                            (cons (cons (closure-name fn) fn) call-env))))
         (meval (closure-body fn) final-env k))))
    ((builtin? fn)
     (apply-k k (apply-builtin (builtin-name fn) args)))
    (else (apply-k k '()))))

(define (eval-args exprs menv k)
  (if (null? exprs) (apply-k k '())
      (meval (car exprs) menv
        (list 'k-args-head (cdr exprs) menv k))))

(define (eval-cond clauses menv k)
  (if (null? clauses) (apply-k k '())
      (let ((clause (car clauses)))
        (if (eq? (car clause) 'else)
            (meval (car (cdr clause)) menv k)
            (meval (car clause) menv
              (list 'k-cond (cdr clauses) (car (cdr clause)) menv k))))))

(define (eval-let-bindings bindings menv k)
  (if (null? bindings) (apply-k k menv)
      (meval (car (cdr (car bindings))) menv
        (list 'k-let-bind (car (car bindings)) (cdr bindings) menv k))))

(define (eval-sequence exprs menv k)
  (if (null? (cdr exprs))
      (meval (car exprs) menv k)
      (meval (car exprs) menv
        (list 'k-seq (cdr exprs) menv k))))

;;; ── Top-level program evaluation ───────────────────────────────────

(define (meval-toplevel expr menv k)
  (cond
    ;; (define (name params) body) — function definition
    ((and (compound? expr) (eq? (car expr) 'define) (pair? (car (cdr expr))))
     (let ((name (car (car (cdr expr))))
           (params (cdr (car (cdr expr))))
           (body (car (cdr (cdr expr)))))
       (let ((closure (make-closure name params body menv)))
         (let ((new-env (cons (cons name closure) menv)))
           (let ((rec-closure (make-closure name params body new-env)))
             (let ((final-env (cons (cons name rec-closure) menv)))
               (apply-k-top k rec-closure final-env)))))))
    ;; Regular expression
    (else
     (meval expr menv (list 'k-define '_ menv k)))))

(define (meval-program exprs menv k)
  (if (null? exprs) (apply-k k '())
      (meval-toplevel (car exprs) menv
        (list 'k-program-step (cdr exprs) k))))

;;; ── Continuation Inspection Utilities ──────────────────────────────

(define (k-next k)
  (let ((tag (car k)))
    (cond
      ((eq? tag 'k-id)             '())
      ((eq? tag 'k-reflect-state)  '())
      ((eq? tag 'k-reflect-jump)   '())
      ((eq? tag 'k-top-id)         '())
      ;; 2 fields
      ((eq? tag 'k-let-body)       (m-nth 2 k))
      ((eq? tag 'k-do-apply)       (m-nth 2 k))
      ((eq? tag 'k-args-tail)      (m-nth 2 k))
      ;; 3 fields
      ((eq? tag 'k-seq)            (m-nth 3 k))
      ((eq? tag 'k-apply-fn)       (m-nth 3 k))
      ((eq? tag 'k-args-head)      (m-nth 3 k))
      ((eq? tag 'k-define)         (m-nth 3 k))
      ;; 4 fields
      ((eq? tag 'k-if)             (m-nth 4 k))
      ((eq? tag 'k-cond)           (m-nth 4 k))
      ((eq? tag 'k-let-bind)       (m-nth 4 k))
      ;; Toplevel
      ((eq? tag 'k-program-step)   (m-nth 2 k))
      (else '()))))

(define (k-depth k)
  (if (null? k) 0
      (if (eq? (car k) 'k-id) 1
          (+ 1 (k-depth (k-next k))))))

(define (k-walk k)
  (if (null? k) '()
      (if (eq? (car k) 'k-id) (list 'k-id)
          (cons (car k) (k-walk (k-next k))))))

;;; ── Base environment ───────────────────────────────────────────────

(define (make-base-env)
  (list
    (cons '+ (make-builtin '+))
    (cons '- (make-builtin '-))
    (cons '* (make-builtin '*))
    (cons '< (make-builtin '<))
    (cons '> (make-builtin '>))
    (cons '= (make-builtin '=))
    (cons 'cons (make-builtin 'cons))
    (cons 'car (make-builtin 'car))
    (cons 'cdr (make-builtin 'cdr))
    (cons 'null? (make-builtin 'null?))
    (cons 'number? (make-builtin 'number?))
    (cons 'pair? (make-builtin 'pair?))
    (cons 'eq? (make-builtin 'eq?))
    (cons 'not (make-builtin 'not))
    (cons 'display (make-builtin 'display))
    (cons 'newline (make-builtin 'newline))
    (cons 'list (make-builtin 'list))
    (cons 'list-ref (make-builtin 'list-ref))))

;;; ── Convenience runner ─────────────────────────────────────────────

(define (mrun expr)
  (meval expr (make-base-env) (list 'k-id)))

(define (mrun-program exprs)
  (meval-program exprs (make-base-env) (list 'k-id)))

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

(display "=== Metacircular Evaluator Tests ===") (newline)

;; Self-evaluating
(check "number" 42 (mrun 42))
(check "boolean" #t (mrun #t))
(check "string" "hello" (mrun '(quote "hello")))

;; Arithmetic
(check "(+ 1 2)" 3 (mrun '(+ 1 2)))
(check "(* 3 4)" 12 (mrun '(* 3 4)))
(check "(- 10 3)" 7 (mrun '(- 10 3)))

;; Nested arithmetic
(check "(+ (* 2 3) (- 10 4))" 12 (mrun '(+ (* 2 3) (- 10 4))))

;; Quote
(check "quote" 42 (mrun '(quote 42)))
(check "quoted list" '(1 2 3) (mrun '(quote (1 2 3))))

;; If
(check "if true"  1 (mrun '(if #t 1 2)))
(check "if false" 2 (mrun '(if #f 1 2)))
(check "if computed" 10 (mrun '(if (< 1 2) 10 20)))

;; Cond
(check "cond" 2 (mrun '(cond (#f 1) (#t 2) (#t 3))))
(check "cond else" 99 (mrun '(cond (#f 1) (else 99))))

;; Lambda
(check "lambda call" 5 (mrun '((lambda (x) (+ x 3)) 2)))
(check "lambda two args" 7 (mrun '((lambda (x y) (+ x y)) 3 4)))

;; Let
(check "let" 30 (mrun '(let ((x 10) (y 20)) (+ x y))))

;; Nested let
(check "nested let" 5 (mrun '(let ((x 1)) (let ((y 2)) (+ x (* y 2)) ))))

;; Begin (sequence)
(check "begin" 3 (mrun '(begin 1 2 3)))

;; Higher-order: lambda returning lambda
(check "higher-order" 15
  (mrun '((lambda (f) (f 5)) (lambda (x) (* x 3)))))

;; Recursive function via program (define + call)
(display "--- Recursive programs ---") (newline)

(check "factorial"
       120
       (mrun-program '(
         (define (fact n)
           (if (< n 2) 1 (* n (fact (- n 1)))))
         (fact 5))))

(check "fibonacci"
       21
       (mrun-program '(
         (define (fib n)
           (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))
         (fib 8))))

;; Continuation inspection
(display "--- Continuation inspection ---") (newline)

(let ((state (mrun '(reify))))
  (check "reify returns list" #t (pair? state))
  (check "reify tag" 'reified-state (car state))
  (let ((k (car (cdr state))))
    (check "continuation is list" #t (pair? k))
    (display "  continuation walk: ") (display (k-walk k)) (newline)
    (display "  continuation depth: ") (display (k-depth k)) (newline)))

;; Summary
(newline)
(display pass) (display " passed, ")
(display fail) (display " failed") (newline)
(if (= fail 0)
    (display "All metacircular evaluator tests passed.")
    (display "SOME TESTS FAILED."))
(newline)
