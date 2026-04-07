;;; pe.scm — Online Partial Evaluator for Scheme
;;;
;;; Takes quoted Scheme s-expressions + known/unknown bindings and
;;; evaluates what it can, residualizing what it can't.
;;;
;;; Run: cargo run -- examples/pe.scm

;;; ── Unknown and residual markers ───────────────────────────────────

(define *unknown-tag* (list 'unknown-tag))
(define (make-unknown name) (cons *unknown-tag* name))
(define (unknown? v) (and (pair? v) (eq? (car v) *unknown-tag*)))
(define (unknown-name v) (cdr v))
(define *unknown* (make-unknown '?))

(define *residual-tag* (list 'residual-tag))
(define (make-residual expr) (cons *residual-tag* expr))
(define (residual? v) (and (pair? v) (eq? (car v) *residual-tag*)))
(define (residual-expr v) (cdr v))

(define (known? v) (and (not (unknown? v)) (not (residual? v))))

;;; ── Function table ─────────────────────────────────────────────────

(define *ftable* '())
(define (register-fn! name params body)
  (set! *ftable* (cons (list name params body) *ftable*)))
(define (lookup-fn name)
  (let loop ((ft *ftable*))
    (if (null? ft) #f
        (if (eq? name (car (car ft))) (car ft) (loop (cdr ft))))))
(define (reset-ftable!) (set! *ftable* '()))

;;; ── Depth limit ────────────────────────────────────────────────────

(define *max-depth* 500)
(define *depth* 0)

;;; ── Environment ────────────────────────────────────────────────────

(define (pe-lookup sym env)
  (let loop ((e env))
    (if (null? e) *unknown*
        (if (eq? sym (car (car e))) (cdr (car e)) (loop (cdr e))))))

(define (pe-extend params vals env)
  (if (null? params) env
      (cons (cons (car params) (car vals))
            (pe-extend (cdr params) (cdr vals) env))))

;;; ── Lifting: value → expression ────────────────────────────────────

(define (pe-lift v)
  (cond
    ((unknown? v) (unknown-name v))
    ((residual? v) (residual-expr v))
    ((number? v) v)
    ((boolean? v) v)
    ((string? v) v)
    ((symbol? v) (list 'quote v))
    ((null? v) (list 'quote '()))
    ((pair? v) (list 'quote v))
    (else v)))

;;; ── The Partial Evaluator ──────────────────────────────────────────

(define (pe-eval expr env)
  (cond
    ((number? expr) expr)
    ((boolean? expr) expr)
    ((string? expr) expr)
    ((symbol? expr)
     (let ((v (pe-lookup expr env)))
       (if (known? v) v (make-unknown expr))))
    ((pair? expr) (pe-eval-compound expr env))
    (else expr)))

(define (pe-eval-compound expr env)
  (let ((head (car expr)))
    (cond
      ((eq? head 'quote)
       (car (cdr expr)))
      ((eq? head 'if)
       (pe-eval-if (cdr expr) env))
      ((eq? head 'cond)
       (pe-eval-cond (cdr expr) env))
      ((eq? head 'let)
       (pe-eval-let (car (cdr expr)) (car (cdr (cdr expr))) env))
      ((eq? head 'begin)
       (pe-eval-begin (cdr expr) env))
      ((memq head '(+ - * quotient remainder))
       (pe-eval-arith head (cdr expr) env))
      ((memq head '(< > = <= >=))
       (pe-eval-cmp head (cdr expr) env))
      ((eq? head 'car)   (pe-eval-car (cdr expr) env))
      ((eq? head 'cdr)   (pe-eval-cdr (cdr expr) env))
      ((eq? head 'cons)  (pe-eval-cons (cdr expr) env))
      ((eq? head 'null?)  (pe-eval-pred null? 'null? (cdr expr) env))
      ((eq? head 'pair?)  (pe-eval-pred pair? 'pair? (cdr expr) env))
      ((eq? head 'number?) (pe-eval-pred number? 'number? (cdr expr) env))
      ((eq? head 'symbol?) (pe-eval-pred symbol? 'symbol? (cdr expr) env))
      ((eq? head 'boolean?) (pe-eval-pred boolean? 'boolean? (cdr expr) env))
      ((eq? head 'string?) (pe-eval-pred string? 'string? (cdr expr) env))
      ((eq? head 'char?)  (pe-eval-pred char? 'char? (cdr expr) env))
      ((eq? head 'eq?)   (pe-eval-eq (cdr expr) env))
      ((eq? head 'equal?) (pe-eval-equal (cdr expr) env))
      ((eq? head 'not)   (pe-eval-not (cdr expr) env))
      ((eq? head 'and)   (pe-eval-and (cdr expr) env))
      ((eq? head 'or)    (pe-eval-or (cdr expr) env))
      ((eq? head 'list)  (pe-eval-list (cdr expr) env))
      (else (pe-eval-call head (cdr expr) env)))))

;;; ── Form handlers ──────────────────────────────────────────────────

(define (pe-eval-if args env)
  (let ((test-val (pe-eval (car args) env)))
    (if (known? test-val)
        (if test-val
            (pe-eval (car (cdr args)) env)
            (pe-eval (car (cdr (cdr args))) env))
        (make-residual
          (list 'if (pe-lift test-val)
                (pe-lift (pe-eval (car (cdr args)) env))
                (pe-lift (pe-eval (car (cdr (cdr args))) env)))))))

(define (pe-eval-cond clauses env)
  (if (null? clauses) *unknown*
      (let ((clause (car clauses)))
        (if (eq? (car clause) 'else)
            (pe-eval (car (cdr clause)) env)
            (let ((test-val (pe-eval (car clause) env)))
              (if (known? test-val)
                  (if test-val
                      (pe-eval (car (cdr clause)) env)
                      (pe-eval-cond (cdr clauses) env))
                  *unknown*))))))

(define (pe-eval-let bindings body env)
  (if (null? bindings)
      (pe-eval body env)
      (let ((var (car (car bindings)))
            (val (pe-eval (car (cdr (car bindings))) env)))
        (pe-eval-let (cdr bindings) body (cons (cons var val) env)))))

(define (pe-eval-begin exprs env)
  (if (null? (cdr exprs))
      (pe-eval (car exprs) env)
      (begin (pe-eval (car exprs) env)
             (pe-eval-begin (cdr exprs) env))))

(define (pe-eval-arith op args env)
  (let ((a (pe-eval (car args) env))
        (b (pe-eval (car (cdr args)) env)))
    (if (and (known? a) (known? b))
        (cond ((eq? op '+) (+ a b)) ((eq? op '-) (- a b))
              ((eq? op '*) (* a b)) ((eq? op 'quotient) (quotient a b))
              ((eq? op 'remainder) (remainder a b)) (else *unknown*))
        (make-residual (list op (pe-lift a) (pe-lift b))))))

(define (pe-eval-cmp op args env)
  (let ((a (pe-eval (car args) env))
        (b (pe-eval (car (cdr args)) env)))
    (if (and (known? a) (known? b))
        (cond ((eq? op '<) (< a b)) ((eq? op '>) (> a b))
              ((eq? op '=) (= a b)) ((eq? op '<=) (<= a b))
              ((eq? op '>=) (>= a b)) (else *unknown*))
        (make-residual (list op (pe-lift a) (pe-lift b))))))

(define (pe-eval-car args env)
  (let ((v (pe-eval (car args) env)))
    (if (and (known? v) (pair? v)) (car v) *unknown*)))

(define (pe-eval-cdr args env)
  (let ((v (pe-eval (car args) env)))
    (if (and (known? v) (pair? v)) (cdr v) *unknown*)))

(define (pe-eval-cons args env)
  (let ((a (pe-eval (car args) env))
        (b (pe-eval (car (cdr args)) env)))
    (if (and (known? a) (known? b)) (cons a b) *unknown*)))

(define (pe-eval-pred pred-fn pred-name args env)
  (let ((v (pe-eval (car args) env)))
    (if (known? v) (pred-fn v) *unknown*)))

(define (pe-eval-eq args env)
  (let ((a (pe-eval (car args) env))
        (b (pe-eval (car (cdr args)) env)))
    (if (and (known? a) (known? b)) (eq? a b) *unknown*)))

(define (pe-eval-equal args env)
  (let ((a (pe-eval (car args) env))
        (b (pe-eval (car (cdr args)) env)))
    (if (and (known? a) (known? b)) (equal? a b) *unknown*)))

(define (pe-eval-not args env)
  (let ((v (pe-eval (car args) env)))
    (if (known? v) (not v) *unknown*)))

(define (pe-eval-and exprs env)
  (if (null? exprs) #t
      (let ((v (pe-eval (car exprs) env)))
        (if (known? v)
            (if v (if (null? (cdr exprs)) v (pe-eval-and (cdr exprs) env)) #f)
            *unknown*))))

(define (pe-eval-or exprs env)
  (if (null? exprs) #f
      (let ((v (pe-eval (car exprs) env)))
        (if (known? v)
            (if v v (pe-eval-or (cdr exprs) env))
            *unknown*))))

;;; ── List construction ──────────────────────────────────────────────
;;; Always build the list — unknown elements stay as unknowns inside it.
;;; This allows continuation frames like (list 'k-if then else env k)
;;; to be constructed even when k is unknown, so apply-k can dispatch
;;; on the known tag.

(define (pe-eval-list args env)
  (if (null? args) '()
      (let ((head (pe-eval (car args) env))
            (tail (pe-eval-list (cdr args) env)))
        (cons head tail))))

;;; ── Function call ──────────────────────────────────────────────────

(define (pe-eval-call fn-name arg-exprs env)
  (let ((entry (lookup-fn fn-name)))
    (if (not entry) *unknown*
        (let ((params (car (cdr entry)))
              (body (car (cdr (cdr entry))))
              (args (pe-eval-args arg-exprs env)))
          (if (>= *depth* *max-depth*)
              (make-residual (cons fn-name (pe-lift-args args)))
              (begin
                (set! *depth* (+ *depth* 1))
                (let ((result (pe-eval body (pe-extend params args '()))))
                  (set! *depth* (- *depth* 1))
                  ;; If body evaluated to generic *unknown* (not a named
                  ;; unknown like (make-unknown 'x)), residualize the call.
                  ;; Named unknowns are valid results (e.g., m-lookup
                  ;; returning an unknown variable's value).
                  (if (eq? result *unknown*)
                      (make-residual (cons fn-name (pe-lift-args args)))
                      result))))))))

(define (pe-eval-args exprs env)
  (if (null? exprs) '()
      (cons (pe-eval (car exprs) env) (pe-eval-args (cdr exprs) env))))

(define (pe-lift-args args)
  (if (null? args) '()
      (cons (pe-lift (car args)) (pe-lift-args (cdr args)))))

;;; ── Convenience ────────────────────────────────────────────────────

(define (pe-result v)
  (if (residual? v) (residual-expr v) v))

(define (pe-specialize fn-name . args)
  (set! *depth* 0)
  (let ((entry (lookup-fn fn-name)))
    (if (not entry)
        (begin (display "pe: unknown function ") (display fn-name) (newline) *unknown*)
        (let ((params (car (cdr entry)))
              (body (car (cdr (cdr entry)))))
          (pe-result (pe-eval body (pe-extend params args '())))))))

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

(display "=== Online Partial Evaluator Tests ===") (newline)

(display "--- Constant folding ---") (newline)
(check "(+ 3 4)" 7 (pe-eval '(+ 3 4) '()))
(check "(* 6 7)" 42 (pe-eval '(* 6 7) '()))
(check "(- 10 3)" 7 (pe-eval '(- 10 3) '()))
(check "(< 1 2)" #t (pe-eval '(< 1 2) '()))
(check "(> 1 2)" #f (pe-eval '(> 1 2) '()))
(check "nested" 12 (pe-eval '(+ (* 2 3) (- 10 4)) '()))

(display "--- Dead branch ---") (newline)
(check "if true" 1 (pe-eval '(if #t 1 2) '()))
(check "if false" 2 (pe-eval '(if #f 1 2) '()))
(check "if computed" 10 (pe-eval '(if (< 1 2) 10 20) '()))

(display "--- Let ---") (newline)
(check "let known" 30 (pe-eval '(let ((x 10) (y 20)) (+ x y)) '()))
(check "let nested" 5 (pe-eval '(let ((x 2)) (let ((y 3)) (+ x y))) '()))

(display "--- List ops ---") (newline)
(check "car" 1 (pe-eval '(car (quote (1 2 3))) '()))
(check "cdr" '(2 3) (pe-eval '(cdr (quote (1 2 3))) '()))
(check "null? empty" #t (pe-eval '(null? (quote ())) '()))
(check "null? pair" #f (pe-eval '(null? (quote (1))) '()))
(check "eq? symbols" #t (pe-eval '(eq? (quote if) (quote if)) '()))
(check "eq? diff" #f (pe-eval '(eq? (quote if) (quote let)) '()))

(display "--- Cond ---") (newline)
(check "cond first" 1 (pe-eval '(cond (#t 1) (#t 2)) '()))
(check "cond second" 2 (pe-eval '(cond (#f 1) (#t 2)) '()))
(check "cond else" 99 (pe-eval '(cond (#f 1) (else 99)) '()))

(display "--- Function unfolding ---") (newline)
(reset-ftable!)
(register-fn! 'fact '(n) '(if (= n 0) 1 (* n (fact (- n 1)))))
(register-fn! 'fib '(n) '(if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))
(register-fn! 'power '(base exp) '(if (= exp 0) 1 (* base (power base (- exp 1)))))

(check "fact(5)" 120 (pe-specialize 'fact 5))
(check "fact(0)" 1 (pe-specialize 'fact 0))
(check "fib(8)" 21 (pe-specialize 'fib 8))
(check "fib(0)" 0 (pe-specialize 'fib 0))
(check "fib(1)" 1 (pe-specialize 'fib 1))
(check "power(2,10)" 1024 (pe-specialize 'power 2 10))

(display "--- Residualization ---") (newline)
(define power-residual (pe-specialize 'power (make-unknown 'base) 3))
(display "  power(base,3) = ") (display power-residual) (newline)
(check "power residual is *" '* (car power-residual))

(define arith-residual (pe-result (pe-eval '(+ x 3) (list (cons 'x (make-unknown 'x))))))
(display "  (+ x 3) = ") (display arith-residual) (newline)
(check "(+ x 3)" '(+ x 3) arith-residual)

(define if-residual (pe-result (pe-eval '(if x 1 2) (list (cons 'x (make-unknown 'x))))))
(display "  (if x 1 2) = ") (display if-residual) (newline)
(check "(if x 1 2)" '(if x 1 2) if-residual)

(newline)
(display pass) (display " passed, ")
(display fail) (display " failed") (newline)
(if (= fail 0)
    (display "All PE tests passed.")
    (display "SOME TESTS FAILED."))
(newline)
