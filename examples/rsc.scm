;;; rsc.scm — Self-hosted WispyScheme compiler
;;;
;;; CPS + closure conversion pipeline, based on Feeley's 90-minute compiler.
;;; Compiles Scheme to standalone Rust binaries via trampoline execution.
;;;
;;; Usage (development in Chez):
;;;   echo '(define (fib n) ...) (display (fib 30)) (newline)' | \
;;;     chez --script examples/rsc.scm > fib.rs && rustc -O -o fib fib.rs
;;;
;;; Usage (bootstrapped via compile.rs):
;;;   cargo run -- --compile examples/rsc.scm > /tmp/rsc.rs
;;;   rustc -O -o /tmp/rsc /tmp/rsc.rs
;;;   echo '...' | /tmp/rsc > out.rs

;;; ════════════════════════════════════════════════════════════════════
;;; Reader
;;; ════════════════════════════════════════════════════════════════════

(define (read-all)
  (let ((x (read)))
    (if (eof-object? x) '()
        (cons x (read-all)))))

;;; ════════════════════════════════════════════════════════════════════
;;; Emit utilities
;;; ════════════════════════════════════════════════════════════════════

(define (emit s) (display s))
(define (emit-line s) (display s) (newline))

(define (emit-ident-char c)
  (cond
    ((char=? c #\-) (display "_"))
    ((char=? c #\?) (display "_p"))
    ((char=? c #\!) (display "_b"))
    ((char=? c #\>) (display "_t"))
    ((char=? c #\<) (display "_l"))
    ((char=? c #\*) (display "_s"))
    ((char=? c #\/) (display "_d"))
    ((char=? c #\=) (display "_e"))
    ((char=? c #\.) (display "__"))
    (else (write-char c))))

(define (emit-ident-chars s i)
  (if (< i (string-length s))
      (begin (emit-ident-char (string-ref s i))
             (emit-ident-chars s (+ i 1)))))

(define (rust-ident sym)
  (let ((s (if (symbol? sym) (symbol->string sym) sym)))
    (cond
      ((equal? s "loop")   (display "r#loop"))
      ((equal? s "if")     (display "if_"))
      ((equal? s "let")    (display "let_"))
      ((equal? s "fn")     (display "fn_"))
      ((equal? s "mut")    (display "mut_"))
      ((equal? s "return") (display "return_"))
      ((equal? s "match")  (display "match_"))
      ((equal? s "type")   (display "type_"))
      ((equal? s "mod")    (display "mod_"))
      ((equal? s "use")    (display "use_"))
      ((equal? s "ref")    (display "ref_"))
      ((equal? s "as")     (display "as_"))
      ((equal? s "in")     (display "in_"))
      ((equal? s "where")  (display "where_"))
      ((equal? s "true")   (display "true_"))
      ((equal? s "false")  (display "false_"))
      ((equal? s "self")   (display "self_"))
      (else (emit-ident-chars s 0)))))

(define (cadr x) (car (cdr x)))
(define (caddr x) (car (cdr (cdr x))))
(define (cadddr x) (car (cdr (cdr (cdr x)))))
(define (cddr x) (cdr (cdr x)))

;;; ════════════════════════════════════════════════════════════════════
;;; AST: tagged lists
;;; ════════════════════════════════════════════════════════════════════

;; Constructors
(define (make-lit val) (list 'lit val))
(define (make-ref var) (list 'ref var))
(define (make-set var expr) (list 'set! var expr))
(define (make-if test then els) (list 'if test then els))
(define (make-prim op args) (cons 'prim (cons op args)))
(define (make-app parts) (cons 'app parts))
(define (make-lam params body) (list 'lam params body))
(define (make-seq exprs) (cons 'seq exprs))

;; Predicates
(define (lit? x) (and (pair? x) (eq? (car x) 'lit)))
(define (ref? x) (and (pair? x) (eq? (car x) 'ref)))
(define (set? x) (and (pair? x) (eq? (car x) 'set!)))
(define (if? x) (and (pair? x) (eq? (car x) 'if)))
(define (prim? x) (and (pair? x) (eq? (car x) 'prim)))
(define (app? x) (and (pair? x) (eq? (car x) 'app)))
(define (lam? x) (and (pair? x) (eq? (car x) 'lam)))
(define (seq? x) (and (pair? x) (eq? (car x) 'seq)))
(define (closure? x) (and (pair? x) (eq? (car x) 'closure)))

;; Accessors
(define (lit-val x) (cadr x))
(define (ref-var x) (cadr x))
(define (set-var x) (cadr x))
(define (set-val x) (caddr x))
(define (if-test x) (cadr x))
(define (if-then x) (caddr x))
(define (if-else x) (cadddr x))
(define (prim-op x) (cadr x))
(define (prim-args x) (cddr x))
(define (app-fn x) (cadr x))
(define (app-args x) (cddr x))
(define (lam-params x) (cadr x))
(define (lam-body x) (caddr x))
(define (seq-exprs x) (cdr x))
(define (closure-id x) (cadr x))
(define (closure-free x) (cddr x))

;;; ════════════════════════════════════════════════════════════════════
;;; Set utilities
;;; ════════════════════════════════════════════════════════════════════

(define (union s1 s2)
  (cond ((null? s1) s2)
        ((memq (car s1) s2) (union (cdr s1) s2))
        (else (cons (car s1) (union (cdr s1) s2)))))

(define (diff s1 s2)
  (cond ((null? s1) '())
        ((memq (car s1) s2) (diff (cdr s1) s2))
        (else (cons (car s1) (diff (cdr s1) s2)))))

(define (union-multi sets)
  (if (null? sets) '()
      (union (car sets) (union-multi (cdr sets)))))

;;; ════════════════════════════════════════════════════════════════════
;;; Free variables
;;; ════════════════════════════════════════════════════════════════════

(define (fv ast)
  (cond
    ((lit? ast) '())
    ((ref? ast) (list (ref-var ast)))
    ((set? ast) (union (list (set-var ast)) (fv (set-val ast))))
    ((if? ast)  (union (fv (if-test ast))
                       (union (fv (if-then ast)) (fv (if-else ast)))))
    ((prim? ast) (union-multi (map fv (prim-args ast))))
    ((app? ast)  (union-multi (map fv (cdr ast)))) ;; cdr skips 'app tag
    ((lam? ast)  (diff (fv (lam-body ast)) (lam-params ast)))
    ((seq? ast)  (union-multi (map fv (seq-exprs ast))))
    ((closure? ast) (closure-free ast)) ;; free vars are listed in the node
    (else '())))

;;; ════════════════════════════════════════════════════════════════════
;;; Variable generation
;;; ════════════════════════════════════════════════════════════════════

(define *gensym-counter* 0)

(define (gensym prefix)
  (set! *gensym-counter* (+ *gensym-counter* 1))
  (string->symbol
    (string-append (if (symbol? prefix) (symbol->string prefix) prefix)
                   "."
                   (number->string *gensym-counter*))))

;;; ════════════════════════════════════════════════════════════════════
;;; Parser: S-expression → AST
;;; ════════════════════════════════════════════════════════════════════

(define *primitives*
  '(+ - * quotient remainder modulo
    < > = <= >=
    zero? positive? negative? number? eq? not
    null? pair? cons car cdr set-car! set-cdr!
    display newline))

(define (primitive? name)
  (memq name *primitives*))

(define (parse expr)
  (cond
    ((number? expr) (make-lit expr))
    ((boolean? expr) (make-lit expr))
    ((symbol? expr) (make-ref expr))
    ((not (pair? expr)) (make-lit expr))
    (else
     (let ((head (car expr)))
       (cond
         ((eq? head 'quote) (make-lit (cadr expr)))

         ((eq? head 'if)
          (make-if (parse (cadr expr))
                   (parse (caddr expr))
                   (if (pair? (cdr (cddr expr)))
                       (parse (cadddr expr))
                       (make-lit #f))))

         ((eq? head 'lambda)
          (make-lam (cadr expr) (parse-body (cddr expr))))

         ((eq? head 'begin)
          (parse-body (cdr expr)))

         ((eq? head 'set!)
          (make-set (cadr expr) (parse (caddr expr))))

         ((eq? head 'let)
          (if (symbol? (cadr expr))
              ;; Named let → letrec-like: (let name ((v e) ...) body)
              ;; Desugar: define name as recursive lambda, then call it
              (let ((name (cadr expr))
                    (bindings (caddr expr))
                    (body (cdr (cddr expr))))
                (parse `((letrec ((,name (lambda ,(map car bindings) ,@body)))
                           ,name)
                         ,@(map cadr bindings))))
              ;; Regular let → ((lambda (vars) body) vals)
              (let ((bindings (cadr expr))
                    (body (cddr expr)))
                (parse `((lambda ,(map car bindings) ,@body)
                         ,@(map cadr bindings))))))

         ((eq? head 'let*)
          (let ((bindings (cadr expr))
                (body (cddr expr)))
            (if (null? bindings)
                (parse-body body)
                (parse `(let (,(car bindings))
                          (let* ,(cdr bindings) ,@body))))))

         ((eq? head 'letrec)
          ;; (letrec ((v1 e1) (v2 e2)) body)
          ;; → (let ((v1 #f) (v2 #f)) (set! v1 e1) (set! v2 e2) body)
          (let ((bindings (cadr expr))
                (body (cddr expr)))
            (parse `(let ,(map (lambda (b) (list (car b) #f)) bindings)
                      ,@(map (lambda (b) `(set! ,(car b) ,(cadr b))) bindings)
                      ,@body))))

         ((eq? head 'cond)
          (parse-cond (cdr expr)))

         ((eq? head 'and)
          (parse-and (cdr expr)))

         ((eq? head 'or)
          (parse-or (cdr expr)))

         ;; Primitive application
         ((and (symbol? head) (primitive? head))
          (make-prim head (map parse (cdr expr))))

         ;; General application
         (else
          (make-app (map parse expr))))))))

(define (parse-body exprs)
  (cond
    ((null? exprs) (make-lit #f))
    ((null? (cdr exprs)) (parse (car exprs)))
    (else (make-seq (map parse exprs)))))

(define (parse-cond clauses)
  (cond
    ((null? clauses) (make-lit #f))
    ((eq? (car (car clauses)) 'else)
     (parse-body (cdr (car clauses))))
    (else
     (make-if (parse (car (car clauses)))
              (parse-body (cdr (car clauses)))
              (parse-cond (cdr clauses))))))

(define (parse-and exprs)
  (cond
    ((null? exprs) (make-lit #t))
    ((null? (cdr exprs)) (parse (car exprs)))
    (else
     (let ((t (gensym 'and)))
       (parse `(let ((,t ,(car exprs)))
                 (if ,t (and ,@(cdr exprs)) ,t)))))))

(define (parse-or exprs)
  (cond
    ((null? exprs) (make-lit #f))
    ((null? (cdr exprs)) (parse (car exprs)))
    (else
     (let ((t (gensym 'or)))
       (parse `(let ((,t ,(car exprs)))
                 (if ,t ,t (or ,@(cdr exprs)))))))))

;;; ════════════════════════════════════════════════════════════════════
;;; CPS conversion (ported from Feeley's 90-minute compiler)
;;; ════════════════════════════════════════════════════════════════════

;;; After CPS, every (app ...) is in tail position.
;;; Lambdas get an extra k parameter.
;;; Administrative redexes: (app (lam ...) vals) = let bindings.

(define (cps ast k)
  (cond
    ;; Atomic: pass directly to continuation
    ((lit? ast)
     (make-app (list k ast)))

    ((ref? ast)
     (make-app (list k ast)))

    ;; Mutation: CPS the value, then set! and pass result to k
    ((set? ast)
     (cps (set-val ast)
          (let ((r (gensym 'r)))
            (make-lam (list r)
              (make-app (list k (make-set (set-var ast) (make-ref r))))))))

    ;; Conditional: CPS the test, then branch
    ((if? ast)
     (let ((test (if-test ast))
           (then-e (if-then ast))
           (else-e (if-else ast)))
       ;; If k is a ref (simple), reuse it in both branches.
       ;; Otherwise, bind k to a variable to prevent code explosion.
       (if (ref? k)
           (cps-list (list test)
             (lambda (test-vals)
               (make-if (car test-vals)
                        (cps then-e k)
                        (cps else-e k))))
           (let ((j (gensym 'k)))
             (make-app
               (list (make-lam (list j)
                       (cps-list (list test)
                         (lambda (test-vals)
                           (make-if (car test-vals)
                                    (cps then-e (make-ref j))
                                    (cps else-e (make-ref j))))))
                     k))))))

    ;; Primitive: CPS all args, then apply prim and pass to k
    ((prim? ast)
     (cps-list (prim-args ast)
       (lambda (args)
         (make-app (list k (make-prim (prim-op ast) args))))))

    ;; Application
    ((app? ast)
     (let ((fn (app-fn ast))
           (args (app-args ast)))
       (if (lam? fn)
           ;; Let binding: (app (lam params body) args)
           ;; CPS the args, bind to params, CPS body with k
           (cps-list args
             (lambda (vals)
               (make-app
                 (cons (make-lam (lam-params fn)
                         (cps (lam-body fn) k))
                       vals))))
           ;; Function call: CPS all parts, then tail-call with k
           (cps-list (cons fn args)
             (lambda (parts)
               (make-app (cons (car parts)     ;; CPS'd function
                               (cons k          ;; continuation
                                     (cdr parts))))))))) ;; CPS'd args

    ;; Lambda: add k parameter, CPS body
    ((lam? ast)
     (let ((j (gensym 'k)))
       (make-app
         (list k
               (make-lam (cons j (lam-params ast))
                 (cps (lam-body ast) (make-ref j)))))))

    ;; Sequence
    ((seq? ast)
     (cps-seq (seq-exprs ast) k))

    (else
     (make-app (list k (make-lit #f))))))

;; CPS a list of expressions, calling (inner cps'd-values) when done.
;; Atomic values pass through unchanged; complex expressions get
;; bound to fresh variables via continuation lambdas.
(define (cps-list asts inner)
  (if (null? asts)
      (inner '())
      (let ((first (car asts))
            (rest (cdr asts)))
        (if (or (lit? first) (ref? first))
            ;; Atomic: pass through
            (cps-list rest
              (lambda (rest-vals)
                (inner (cons first rest-vals))))
            ;; Complex: CPS it, bind result to fresh var
            (let ((r (gensym 'r)))
              (cps first
                (make-lam (list r)
                  (cps-list rest
                    (lambda (rest-vals)
                      (inner (cons (make-ref r) rest-vals)))))))))))

;; CPS a sequence of expressions
(define (cps-seq asts k)
  (cond
    ((null? asts) (make-app (list k (make-lit #f))))
    ((null? (cdr asts)) (cps (car asts) k))
    (else
     (let ((r (gensym 'r)))
       (cps (car asts)
         (make-lam (list r)
           (cps-seq (cdr asts) k)))))))

;; Top-level CPS entry: wrap with %halt continuation
(define (cps-convert ast)
  (let ((r (gensym 'r)))
    (cps ast
      (make-lam (list r)
        (make-prim '%halt (list (make-ref r)))))))

;;; ════════════════════════════════════════════════════════════════════
;;; Lambda collection: walk CPS'd AST, collect all lambdas
;;; ════════════════════════════════════════════════════════════════════

;; Each collected lambda: (id params free-vars body)
(define *lambdas* '())
(define *next-id* 0)
(define *globals* '())    ;; known top-level function names
(define *global-ids* '()) ;; ((name . id) ...) for global functions

(define (add-lambda! params body)
  (let ((id *next-id*)
        (free (diff (diff (fv body) params) *globals*)))
    (set! *next-id* (+ *next-id* 1))
    (set! *lambdas* (cons (list id params free body) *lambdas*))
    id))

(define (lambda-id l) (car l))
(define (lambda-params l) (cadr l))
(define (lambda-free l) (caddr l))
(define (lambda-body l) (cadddr l))

;; Walk AST and replace (lam ...) nodes with (closure id free-vars...)
;; This is a combined closure-convert + lambda-lift pass.
(define (lift ast)
  (cond
    ((lit? ast) ast)
    ((ref? ast) ast)
    ((set? ast) (make-set (set-var ast) (lift (set-val ast))))
    ((if? ast)  (make-if (lift (if-test ast))
                         (lift (if-then ast))
                         (lift (if-else ast))))
    ((prim? ast) (make-prim (prim-op ast) (map lift (prim-args ast))))
    ((app? ast)
     (let ((fn (app-fn ast)))
       (if (lam? fn)
           ;; Administrative redex (let binding): lift body, keep structure
           (make-app (cons (make-lam (lam-params fn) (lift (lam-body fn)))
                           (map lift (app-args ast))))
           ;; Regular call: lift all parts
           (make-app (map lift (cdr ast))))))
    ((lam? ast)
     ;; Lambda in value position: lift body, collect, return closure node
     (let* ((body (lift (lam-body ast)))
            (id (add-lambda! (lam-params ast) body))
            (free (diff (diff (fv body) (lam-params ast)) *globals*)))
       (cons 'closure (cons id free))))
    ((seq? ast)
     (make-seq (map lift (seq-exprs ast))))
    (else ast)))

;;; ════════════════════════════════════════════════════════════════════
;;; Rust code emission
;;; ════════════════════════════════════════════════════════════════════

;; ── Emit a value expression (not in tail position) ──

(define (emit-val ast)
  (cond
    ((lit? ast)
     (let ((v (lit-val ast)))
       (cond
         ((number? v)
          (emit "Val::fixnum(") (emit v) (emit ")"))
         ((eq? v #t) (emit "TRUE_VAL"))
         ((eq? v #f) (emit "FALSE_VAL"))
         ((null? v) (emit "Val::NIL"))
         (else (emit "Val::NIL")))))

    ((ref? ast)
     (let ((name (ref-var ast)))
       (let ((gid (assq name *global-ids*)))
         (if gid
             (begin (emit "make_closure(") (emit (cdr gid)) (emit ", Val::NIL)"))
             (rust-ident name)))))

    ((set? ast)
     (emit "{ ")
     (rust-ident (set-var ast))
     (emit " = ")
     (emit-val (set-val ast))
     (emit "; Val::NIL }"))

    ((prim? ast)
     (emit-prim (prim-op ast) (prim-args ast)))

    ((closure? ast)
     (let ((id (closure-id ast))
           (free (closure-free ast)))
       (if (null? free)
           (begin (emit "make_closure(") (emit id) (emit ", Val::NIL)"))
           (begin (emit "make_closure(") (emit id) (emit ", ")
                  (emit-env-build free)
                  (emit ")")))))

    ((app? ast)
     ;; (app (lam ...) args) = let binding in value position
     (if (lam? (app-fn ast))
         (begin
           (emit "{ ")
           (emit-let-bindings (lam-params (app-fn ast)) (app-args ast))
           (emit-val (lam-body (app-fn ast)))
           (emit " }"))
         ;; Shouldn't happen in CPS (all non-let apps are in tail position)
         (begin (emit "Val::NIL /* unexpected app in value position */"))))

    ((if? ast)
     (emit "if is_true(")
     (emit-val (if-test ast))
     (emit ") { ")
     (emit-val (if-then ast))
     (emit " } else { ")
     (emit-val (if-else ast))
     (emit " }"))

    (else (emit "Val::NIL"))))

;; Emit a primitive operation as a Rust value expression
(define (emit-prim op args)
  (cond
    ;; Arithmetic → Val::fixnum(a_raw op b_raw)
    ((memq op '(+ - * quotient remainder modulo))
     (let ((rust-op (cond ((eq? op '+) " + ")
                          ((eq? op '-) " - ")
                          ((eq? op '*) " * ")
                          ((eq? op 'quotient) " / ")
                          ((eq? op 'remainder) " % ")
                          ((eq? op 'modulo) " % ")
                          (else " + "))))
       (if (and (eq? op '-) (null? (cdr args)))
           ;; Unary minus
           (begin (emit "Val::fixnum(-")
                  (emit-i64 (car args))
                  (emit ")"))
           (begin (emit "Val::fixnum(")
                  (emit-i64 (car args))
                  (emit rust-op)
                  (emit-i64 (cadr args))
                  (emit ")")))))

    ;; Comparisons → bool_to_val(a_raw cmp b_raw)
    ((memq op '(< > = <= >=))
     (let ((rust-op (cond ((eq? op '<) " < ")
                          ((eq? op '>) " > ")
                          ((eq? op '=) " == ")
                          ((eq? op '<=) " <= ")
                          ((eq? op '>=) " >= ")
                          (else " == "))))
       (emit "bool_to_val(")
       (emit-i64 (car args))
       (emit rust-op)
       (emit-i64 (cadr args))
       (emit ")")))

    ;; Predicates
    ((eq? op 'zero?)
     (emit "bool_to_val(") (emit-i64 (car args)) (emit " == 0)"))
    ((eq? op 'positive?)
     (emit "bool_to_val(") (emit-i64 (car args)) (emit " > 0)"))
    ((eq? op 'negative?)
     (emit "bool_to_val(") (emit-i64 (car args)) (emit " < 0)"))
    ((eq? op 'number?)
     (emit "bool_to_val(") (emit-val (car args)) (emit ".is_fixnum())"))
    ((eq? op 'null?)
     (emit "bool_to_val(") (emit-val (car args)) (emit " == Val::NIL)"))
    ((eq? op 'pair?)
     (emit "bool_to_val({ let __v = ") (emit-val (car args))
     (emit "; __v != Val::NIL && !__v.is_fixnum() && unsafe { HEAP[__v.as_rib()].tag == TAG_PAIR } })"))
    ((eq? op 'eq?)
     (emit "bool_to_val(") (emit-val (car args)) (emit " == ") (emit-val (cadr args)) (emit ")"))
    ((eq? op 'not)
     (emit "bool_to_val(!is_true(") (emit-val (car args)) (emit "))"))

    ;; Pair ops
    ((eq? op 'cons)
     (emit "cons(") (emit-val (car args)) (emit ", ") (emit-val (cadr args)) (emit ")"))
    ((eq? op 'car)
     (emit "car(") (emit-val (car args)) (emit ")"))
    ((eq? op 'cdr)
     (emit "cdr(") (emit-val (car args)) (emit ")"))
    ((eq? op 'set-car!)
     (emit "{ set_car(") (emit-val (car args)) (emit ", ") (emit-val (cadr args)) (emit "); Val::NIL }"))
    ((eq? op 'set-cdr!)
     (emit "{ set_cdr(") (emit-val (car args)) (emit ", ") (emit-val (cadr args)) (emit "); Val::NIL }"))

    ;; I/O
    ((eq? op 'display)
     (emit "{ display(") (emit-val (car args)) (emit "); Val::NIL }"))
    ((eq? op 'newline)
     (emit "{ println!(); Val::NIL }"))

    ;; %halt — used by CPS as program terminator
    ((eq? op '%halt)
     (emit "{ display(") (emit-val (car args)) (emit "); Val::NIL }"))

    (else
     (emit "Val::NIL /* unknown prim ") (emit op) (emit " */"))))

;; Emit an expression as raw i64 (for arithmetic operands)
(define (emit-i64 ast)
  (cond
    ((lit? ast)
     (let ((v (lit-val ast)))
       (if (< v 0)
           (begin (emit "(") (emit v) (emit "i64)"))
           (begin (emit v) (emit "i64")))))
    ((prim? ast)
     ;; Nested arithmetic → recurse in i64 mode
     (let ((op (prim-op ast))
           (args (prim-args ast)))
       (cond
         ((memq op '(+ - * quotient remainder modulo))
          (let ((rust-op (cond ((eq? op '+) " + ")
                               ((eq? op '-) " - ")
                               ((eq? op '*) " * ")
                               ((eq? op 'quotient) " / ")
                               ((eq? op 'remainder) " % ")
                               ((eq? op 'modulo) " % ")
                               (else " + "))))
            (if (and (eq? op '-) (null? (cdr args)))
                (begin (emit "(-") (emit-i64 (car args)) (emit ")"))
                (begin (emit "(") (emit-i64 (car args)) (emit rust-op)
                       (emit-i64 (cadr args)) (emit ")")))))
         (else
          ;; Not arithmetic prim — fall back to Val unwrap
          (emit-val ast) (emit ".as_fixnum().unwrap()")))))
    (else
     ;; Variable or other → emit as Val and unwrap
     (emit-val ast) (emit ".as_fixnum().unwrap()"))))

;; Emit cons chain to build environment from free variable list
(define (emit-env-build free-vars)
  (if (null? free-vars)
      (emit "Val::NIL")
      (begin
        (emit "cons(")
        (rust-ident (car free-vars))
        (emit ", ")
        (emit-env-build (cdr free-vars))
        (emit ")"))))

;; Emit let bindings for administrative redex
(define (emit-let-bindings params args)
  (if (pair? params)
      (begin
        (emit "let ")
        (rust-ident (car params))
        (emit " = ")
        (emit-val (car args))
        (emit "; ")
        (emit-let-bindings (cdr params) (cdr args)))))

;; ── Emit a tail-position expression (returns Action) ──

;; Emit a tail call: all-parts = (fn arg1 arg2 ...)
(define (emit-tail-call all-parts)
  (let ((nargs (- (length all-parts) 1)))
    (cond
      ((= nargs 1)
       (emit "Action::Call1(")
       (emit-val (car all-parts))
       (emit ", ")
       (emit-val (cadr all-parts))
       (emit ")"))
      ((= nargs 2)
       (emit "Action::Call2(")
       (emit-val (car all-parts))
       (emit ", ")
       (emit-val (cadr all-parts))
       (emit ", ")
       (emit-val (caddr all-parts))
       (emit ")"))
      ((= nargs 3)
       (emit "Action::Call3(")
       (emit-val (car all-parts))
       (emit ", ")
       (emit-val (cadr all-parts))
       (emit ", ")
       (emit-val (caddr all-parts))
       (emit ", ")
       (emit-val (cadddr all-parts))
       (emit ")"))
      (else
       (emit "Action::CallN(")
       (emit-val (car all-parts))
       (emit ", vec![")
       (emit-val-list (cdr all-parts))
       (emit "])")))))

(define (emit-tail ast)
  (cond
    ;; Application in tail position
    ((app? ast)
     (let ((fn (app-fn ast)))
       (if (lam? fn)
           ;; Administrative redex (let binding): emit bindings, body in tail
           (begin
             (emit "{ ")
             (emit-let-bindings (lam-params fn) (app-args ast))
             (emit-tail (lam-body fn))
             (emit " }"))
           ;; Real tail call → Action
           (emit-tail-call (cdr ast)))))

    ;; If in tail position: both branches are tail
    ((if? ast)
     (emit "if is_true(")
     (emit-val (if-test ast))
     (emit ") { ")
     (emit-tail (if-then ast))
     (emit " } else { ")
     (emit-tail (if-else ast))
     (emit " }"))

    ;; Seq in tail position: all but last are values, last is tail
    ((seq? ast)
     (let ((es (seq-exprs ast)))
       (emit "{ ")
       (emit-seq-tail es)
       (emit " }")))

    ;; Prim in tail position: shouldn't happen after CPS unless it's %halt
    ((prim? ast)
     (if (eq? (prim-op ast) '%halt)
         (begin (emit "Action::Halt(") (emit-val (car (prim-args ast))) (emit ")"))
         ;; Other prims in tail: wrap as Action::Halt (shouldn't normally happen)
         (begin (emit "Action::Halt(") (emit-prim (prim-op ast) (prim-args ast)) (emit ")"))))

    ;; Lit/ref in tail position: shouldn't happen after CPS
    (else
     (emit "Action::Halt(")
     (emit-val ast)
     (emit ")"))))

(define (emit-val-list vals)
  (if (pair? vals)
      (begin
        (emit-val (car vals))
        (if (pair? (cdr vals))
            (begin (emit ", ") (emit-val-list (cdr vals)))))))

(define (emit-seq-tail exprs)
  (cond
    ((null? (cdr exprs))
     (emit-tail (car exprs)))
    (else
     (emit "let _ = ")
     (emit-val (car exprs))
     (emit "; ")
     (emit-seq-tail (cdr exprs)))))

;; ── Emit environment extraction for a lambda function ──

(define (emit-env-extract free-vars)
  (let loop ((vars free-vars) (depth 0))
    (if (pair? vars)
        (begin
          (emit "    let ")
          (rust-ident (car vars))
          (emit " = ")
          (if (= depth 0)
              (emit "car(__env)")
              (begin
                (emit "car(")
                (let inner ((d depth))
                  (if (= d 0)
                      (emit "__env")
                      (begin (emit "cdr(") (inner (- d 1)) (emit ")"))))
                (emit ")")))
          (emit ";")
          (newline)
          (loop (cdr vars) (+ depth 1))))))

;; ── Emit a single lambda function ──

(define (emit-lambda lam)
  (let ((id (lambda-id lam))
        (params (lambda-params lam))
        (free (lambda-free lam))
        (body (lambda-body lam)))
    (emit "fn __lambda_") (emit id) (emit "(__env: Val")
    ;; Parameters
    (for-each (lambda (p)
                (emit ", ")
                (rust-ident p)
                (emit ": Val"))
              params)
    (emit ") -> Action {")
    (newline)
    ;; Extract free variables from environment
    (emit-env-extract free)
    ;; Body (in tail position)
    (emit "    ")
    (emit-tail body)
    (newline)
    (emit "}")
    (newline)
    (newline)))

;; ── Emit dispatch_cps ──

(define (emit-dispatch)
  (emit-line "fn dispatch_cps(closure: Val, args: &[Val]) -> Action {")
  (emit-line "    let code_id = car(closure).as_fixnum().unwrap();")
  (emit-line "    let __env = cdr(closure);")
  (emit-line "    match code_id {")
  ;; Emit each lambda's dispatch case
  (for-each
    (lambda (lam)
      (let ((id (lambda-id lam))
            (params (lambda-params lam)))
        (emit "        ") (emit id) (emit " => __lambda_") (emit id) (emit "(__env")
        (let loop ((i 0) (ps params))
          (if (pair? ps)
              (begin
                (emit ", args[") (emit i) (emit "]")
                (loop (+ i 1) (cdr ps)))))
        (emit "),")
        (newline)))
    (reverse *lambdas*))
  (emit-line "        _ => Action::Halt(Val::NIL),")
  (emit-line "    }")
  (emit-line "}")
  (newline))

;; ── Emit Rust runtime ──

(define (emit-runtime)
  (emit-line "// Generated by rsc.scm — CPS + closure conversion pipeline")
  (emit-line "#![allow(non_snake_case, unused_variables, unused_mut, unused_parens, dead_code, unreachable_code)]")
  (newline)
  ;; Val type
  (emit-line "#[derive(Clone, Copy, PartialEq, Eq)]")
  (emit-line "struct Val(i64);")
  (newline)
  (emit-line "impl Val {")
  (emit-line "    const NIL: Val = Val(0);")
  (emit-line "    #[inline(always)] const fn fixnum(n: i64) -> Val { Val((n << 1) | 1) }")
  (emit-line "    #[inline(always)] fn is_fixnum(self) -> bool { (self.0 & 1) != 0 }")
  (emit-line "    #[inline(always)] fn as_fixnum(self) -> Option<i64> { if self.is_fixnum() { Some(self.0 >> 1) } else { None } }")
  (emit-line "    #[inline(always)] fn as_rib(self) -> usize { (self.0 >> 1) as usize }")
  (emit-line "}")
  (newline)
  (emit-line "impl std::fmt::Display for Val {")
  (emit-line "    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {")
  (emit-line "        if let Some(n) = self.as_fixnum() { write!(f, \"{}\", n) }")
  (emit-line "        else if *self == Val::NIL { write!(f, \"()\") }")
  (emit-line "        else { write!(f, \"#<rib>\") }")
  (emit-line "    }")
  (emit-line "}")
  (newline)
  ;; Constants
  (emit-line "const FALSE_VAL: Val = Val(1 << 1);")
  (emit-line "const TRUE_VAL: Val = Val(2 << 1);")
  (emit-line "const TAG_PAIR: u8 = 12;")
  (emit-line "const TAG_CLS: u8 = 14;")
  (newline)
  ;; Rib heap
  (emit-line "#[derive(Clone, Copy)]")
  (emit-line "struct Rib { car: Val, cdr: Val, tag: u8 }")
  (emit-line "static mut HEAP: Vec<Rib> = Vec::new();")
  (newline)
  (emit-line "fn heap_init() { unsafe {")
  (emit-line "    HEAP = Vec::with_capacity(1 << 20);")
  (emit-line "    HEAP.push(Rib { car: Val::NIL, cdr: Val::NIL, tag: 0 }); // rib 0: nil")
  (emit-line "    HEAP.push(Rib { car: Val::NIL, cdr: Val::NIL, tag: 0 }); // rib 1: #f")
  (emit-line "    HEAP.push(Rib { car: Val::NIL, cdr: Val::NIL, tag: 0 }); // rib 2: #t")
  (emit-line "}}")
  (newline)
  (emit-line "#[inline(always)]")
  (emit-line "fn alloc_rib(car: Val, cdr: Val, tag: u8) -> Val {")
  (emit-line "    unsafe { let idx = HEAP.len(); HEAP.push(Rib { car, cdr, tag }); Val((idx as i64) << 1) }")
  (emit-line "}")
  (newline)
  (emit-line "#[inline(always)] fn cons(car: Val, cdr: Val) -> Val { alloc_rib(car, cdr, TAG_PAIR) }")
  (emit-line "#[inline(always)] fn car(v: Val) -> Val { if v.is_fixnum() || v == Val::NIL { Val::NIL } else { unsafe { HEAP[v.as_rib()].car } } }")
  (emit-line "#[inline(always)] fn cdr(v: Val) -> Val { if v.is_fixnum() || v == Val::NIL { Val::NIL } else { unsafe { HEAP[v.as_rib()].cdr } } }")
  (emit-line "#[inline(always)] fn set_car(v: Val, c: Val) { if !v.is_fixnum() && v != Val::NIL { unsafe { HEAP[v.as_rib()].car = c; } } }")
  (emit-line "#[inline(always)] fn set_cdr(v: Val, c: Val) { if !v.is_fixnum() && v != Val::NIL { unsafe { HEAP[v.as_rib()].cdr = c; } } }")
  (newline)
  (emit-line "#[inline(always)]")
  (emit-line "fn make_closure(code_id: i64, env: Val) -> Val { alloc_rib(Val::fixnum(code_id), env, TAG_CLS) }")
  (newline)
  (emit-line "#[inline(always)] fn is_true(v: Val) -> bool { v != FALSE_VAL }")
  (emit-line "#[inline(always)] fn bool_to_val(b: bool) -> Val { if b { TRUE_VAL } else { FALSE_VAL } }")
  (newline)
  ;; Display
  (emit-line "fn display(v: Val) { if let Some(n) = v.as_fixnum() { print!(\"{}\", n); } else if v == Val::NIL { print!(\"()\"); } else if v == TRUE_VAL { print!(\"#t\"); } else if v == FALSE_VAL { print!(\"#f\"); } else { print!(\"#<rib>\"); } }")
  (newline)
  ;; Action enum + trampoline
  (emit-line "enum Action {")
  (emit-line "    Call1(Val, Val),")
  (emit-line "    Call2(Val, Val, Val),")
  (emit-line "    Call3(Val, Val, Val, Val),")
  (emit-line "    CallN(Val, Vec<Val>),")
  (emit-line "    Halt(Val),")
  (emit-line "}")
  (newline)
  (emit-line "fn trampoline(func: Val, args: &[Val]) -> Val {")
  (emit-line "    let mut action = dispatch_cps(func, args);")
  (emit-line "    loop {")
  (emit-line "        match action {")
  (emit-line "            Action::Halt(v) => return v,")
  (emit-line "            Action::Call1(f, a) => action = dispatch_cps(f, &[a]),")
  (emit-line "            Action::Call2(f, a, b) => action = dispatch_cps(f, &[a, b]),")
  (emit-line "            Action::Call3(f, a, b, c) => action = dispatch_cps(f, &[a, b, c]),")
  (emit-line "            Action::CallN(f, ref args) => action = dispatch_cps(f, args),")
  (emit-line "        }")
  (emit-line "    }")
  (emit-line "}")
  (newline))

;;; ════════════════════════════════════════════════════════════════════
;;; Main driver
;;; ════════════════════════════════════════════════════════════════════

(define (define? form) (and (pair? form) (eq? (car form) 'define)))

(define (func-name def)
  (if (pair? (cadr def)) (car (cadr def)) (cadr def)))

(define (func-params def)
  (if (pair? (cadr def)) (cdr (cadr def)) '()))

(define (func-body def)
  (if (pair? (cadr def)) (cddr def) (list (caddr def))))

(define (compile-program forms)
  (let* ((defines (filter define? forms))
         (exprs (filter (lambda (x) (not (define? x))) forms))
         ;; Register known function names (for the parser)
         (func-names (map func-name defines)))

    ;; Reset state
    (set! *lambdas* '())
    (set! *next-id* 0)
    (set! *gensym-counter* 0)
    (set! *globals* func-names)
    (set! *global-ids* '())

    ;; Phase 1: Parse each function body and the top-level expressions
    ;; Phase 2: CPS-convert each function (adding k parameter)
    ;; Phase 3: Lift all lambdas (closure-convert + collect)
    (let ((lifted-funcs
            (map (lambda (def)
                   (let* ((name (func-name def))
                          (params (func-params def))
                          (body-ast (parse-body (func-body def)))
                          ;; CPS: the body gets a k parameter
                          (k (gensym 'k))
                          (cps-body (cps body-ast (make-ref k)))
                          ;; Lift lambdas from CPS'd body
                          (lifted-body (lift cps-body))
                          ;; Register this function as a lambda with (k . params)
                          (id (add-lambda! (cons k params) lifted-body))
                          (free (diff (fv lifted-body) (cons k params))))
                     ;; Record global name → ID mapping
                     (set! *global-ids* (cons (cons name id) *global-ids*))
                     (list name id params free)))
                 defines))
          ;; CPS + lift top-level expressions
          (entry-ast
            (if (null? exprs)
                (make-prim '%halt (list (make-lit 0)))
                (let* ((body-ast (parse-body exprs))
                       (cps-body (cps-convert body-ast))
                       (lifted-body (lift cps-body)))
                  lifted-body))))

      ;; Register entry point as a lambda (no params, no free vars)
      (let ((entry-id (add-lambda! '() entry-ast)))

        ;; Emit everything
        (emit-runtime)

        ;; Emit all lambda functions
        (for-each emit-lambda (reverse *lambdas*))

        ;; Emit dispatch
        (emit-dispatch)

        ;; Emit main
        (emit-line "fn main() {")
        (emit-line "    heap_init();")
        (emit "    let result = trampoline(make_closure(")
        (emit entry-id)
        (emit-line ", Val::NIL), &[]);")
        (emit-line "    let _ = result;")
        (emit-line "}")))))

;; Simple filter (in case host Scheme doesn't have it)
(define (filter pred lst)
  (cond ((null? lst) '())
        ((pred (car lst)) (cons (car lst) (filter pred (cdr lst))))
        (else (filter pred (cdr lst)))))

;; Entry point
(compile-program (read-all))
