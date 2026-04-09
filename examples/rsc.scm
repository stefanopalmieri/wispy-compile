;;; rsc.scm — Self-hosted WispyScheme compiler
;;;
;;; CPS + closure conversion pipeline, based on Feeley's 90-minute compiler.
;;; Compiles Scheme to standalone Rust binaries via trampoline execution.
;;;
;;; Usage (wispy-vm):
;;;   echo '(define (fib n) ...) (display (fib 30)) (newline)' | \
;;;     wispy examples/rsc.scm > fib.rs && rustc -O -o fib fib.rs
;;;
;;; Self-compilation:
;;;   wispy examples/rsc.scm < examples/rsc.scm > /tmp/rsc.rs
;;;   rustc -O -o /tmp/rsc /tmp/rsc.rs
;;;   echo '...' | /tmp/rsc > out.rs

(import (scheme base) (scheme read) (scheme write) (scheme char))

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
  ;; Prefix all user identifiers to avoid colliding with Rust keywords
  ;; or runtime function names (car, cdr, cons, display, etc.)
  (let ((s (if (symbol? sym) (symbol->string sym) sym)))
    (emit "__v_")
    (emit-ident-chars s 0)))

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

;; Continuation (CPS-internal lambda, defunctionalized separately from user closures)
(define (make-cont params body) (list 'cont params body))
(define (cont? x) (and (pair? x) (eq? (car x) 'cont)))
(define (cont-params x) (cadr x))
(define (cont-body x) (caddr x))
(define (cont-closure? x) (and (pair? x) (eq? (car x) 'cont-closure)))
(define (cont-closure-id x) (cadr x))
(define (cont-closure-free x) (cddr x))

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

;; Rest-arg helpers: params can be improper list (x y . rest)
;; or a bare symbol (lambda args body)
(define (params-proper params)
  ;; Return the proper (fixed) part of a param list
  (cond ((null? params) '())
        ((symbol? params) '())  ;; bare symbol = all rest
        ((pair? params) (cons (car params) (params-proper (cdr params))))
        (else '())))

(define (params-rest params)
  ;; Return the rest param name, or #f if none
  (cond ((null? params) #f)
        ((symbol? params) params)  ;; bare symbol = rest param
        ((pair? params) (params-rest (cdr params)))
        (else #f)))

(define (params-all params)
  ;; Return a flat list of ALL param names (proper + rest)
  (let ((rest (params-rest params)))
    (if rest
        (append (params-proper params) (list rest))
        (params-proper params))))
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

(define (list-index x lst)
  (let loop ((l lst) (i 0))
    (cond ((null? l) 0)
          ((eq? x (car l)) i)
          (else (loop (cdr l) (+ i 1))))))

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
    ((lam? ast)  (diff (fv (lam-body ast)) (params-all (lam-params ast))))
    ((cont? ast) (diff (fv (cont-body ast)) (params-all (cont-params ast))))
    ((seq? ast)  (union-multi (map fv (seq-exprs ast))))
    ((closure? ast) (closure-free ast)) ;; free vars are listed in the node
    ((cont-closure? ast) (cont-closure-free ast))
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
    zero? positive? negative? number? eq? eqv? equal? not
    null? pair? symbol? string? boolean? char? procedure? eof-object?
    cons car cdr set-car! set-cdr!
    list append reverse length
    display newline write-char read
    string-length string-ref string-append
    string->symbol symbol->string number->string string->number
    char->integer integer->char
    apply error
    char=? memq assq assoc map for-each
    make-vector vector-ref vector-set! vector-length vector? vector->list list->vector))

(define (primitive? name)
  (memq name *primitives*))

;; Arity table for primitives (used for eta-expansion)
(define (prim-arity name)
  (cond
    ((memq name '(car cdr null? pair? symbol? string? boolean? char?
                  procedure? number? not zero? positive? negative?
                  eof-object? display newline write-char read
                  string-length symbol->string number->string string->number
                  char->integer integer->char error reverse length
                  vector-length vector? vector->list list->vector))
     1)
    ((memq name '(+ - * quotient remainder modulo < > = <= >=
                  eq? eqv? equal? cons set-car! set-cdr!
                  string-ref string-append string->symbol
                  char=? memq assq assoc map for-each append apply
                  make-vector vector-ref))
     2)
    ((memq name '(vector-set!))
     3)
    (else 2))) ;; default to 2

;; Eta-expand a primitive: car → (lambda (__a) (car __a))
(define (prim-eta name)
  (let ((arity (prim-arity name)))
    (cond
      ((= arity 0) `(lambda () (,name)))
      ((= arity 1) `(lambda (__a) (,name __a)))
      ((= arity 2) `(lambda (__a __b) (,name __a __b)))
      (else `(lambda (__a __b __c) (,name __a __b __c))))))

(define (parse expr)
  (cond
    ((number? expr) (make-lit expr))
    ((boolean? expr) (make-lit expr))
    ((symbol? expr)
     ;; If a primitive name is used as a value (not in call position),
     ;; wrap it in a lambda so it becomes a first-class closure.
     (if (primitive? expr)
         (parse (prim-eta expr))
         (make-ref expr)))
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

         ((eq? head 'when)
          (make-if (parse (cadr expr))
                   (parse-body (cddr expr))
                   (make-lit #f)))

         ((eq? head 'unless)
          (make-if (parse (cadr expr))
                   (make-lit #f)
                   (parse-body (cddr expr))))

         ((eq? head 'cond)
          (parse-cond (cdr expr)))

         ((eq? head 'and)
          (parse-and (cdr expr)))

         ((eq? head 'or)
          (parse-or (cdr expr)))

         ((eq? head 'case)
          ;; (case expr ((datum ...) body ...) ... (else body ...))
          ;; → (let ((__case-key expr)) (cond ((memv __case-key '(datum ...)) body ...) ...))
          (let ((key (gensym 'case)))
            (parse `(let ((,key ,(cadr expr)))
                      (cond ,@(map (lambda (clause)
                                     (if (eq? (car clause) 'else)
                                         clause
                                         `((memq ,key (quote ,(car clause)))
                                           ,@(cdr clause))))
                                   (cddr expr)))))))

         ((eq? head 'do)
          ;; (do ((var init step) ...) (test result ...) body ...)
          ;; → (let loop ((var init) ...) (if test (begin result ...) (begin body ... (loop step ...))))
          (let ((bindings (cadr expr))
                (test-clause (caddr expr))
                (body (cdr (cddr expr)))
                (loop (gensym 'do)))
            (parse `(let ,loop ,(map (lambda (b) (list (car b) (cadr b))) bindings)
                      (if ,(car test-clause)
                          (begin ,@(if (null? (cdr test-clause))
                                       '(#f)
                                       (cdr test-clause)))
                          (begin ,@body
                                 (,loop ,@(map (lambda (b)
                                                 (if (null? (cddr b))
                                                     (car b)   ;; no step → reuse var
                                                     (caddr b)))
                                               bindings))))))))

         ((eq? head 'quasiquote)
          (parse (expand-qq (cadr expr))))

         ;; Primitive application
         ((and (symbol? head) (primitive? head))
          (make-prim head (map parse (cdr expr))))

         ;; General application
         (else
          (make-app (map parse expr))))))))

(define (parse-body exprs)
  ;; Handle internal defines: collect leading (define ...) forms,
  ;; convert to letrec, then parse the rest as the body.
  (let collect ((es exprs) (defs '()))
    (if (and (pair? es)
             (pair? (car es))
             (eq? (car (car es)) 'define))
        (collect (cdr es) (cons (car es) defs))
        ;; defs collected (reversed); es is the remaining body
        (if (null? defs)
            ;; No internal defines — original behavior
            (cond
              ((null? es) (make-lit #f))
              ((null? (cdr es)) (parse (car es)))
              (else (make-seq (map parse es))))
            ;; Convert internal defines to letrec
            (let ((bindings
                    (map (lambda (d)
                           (if (pair? (cadr d))
                               ;; (define (f args...) body...) → (f (lambda (args...) body...))
                               (list (car (cadr d))
                                     (cons 'lambda (cons (cdr (cadr d)) (cddr d))))
                               ;; (define x expr) → (x expr)
                               (list (cadr d) (caddr d))))
                         (reverse defs))))
              (parse (cons 'letrec (cons bindings es))))))))

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
;;; Quasiquote expansion
;;; ════════════════════════════════════════════════════════════════════

;; Expand quasiquote template into explicit cons/list/append calls.
;; (expand-qq x) returns a Scheme expression (not AST) that, when
;; evaluated, builds the same structure as `x with , and ,@ expanded.

(define (expand-qq x)
  (cond
    ((not (pair? x))
     ;; Atom → (quote atom)
     (list 'quote x))
    ((eq? (car x) 'unquote)
     ;; ,expr → expr (unevaluated — parse will handle it)
     (cadr x))
    ((and (pair? (car x)) (eq? (car (car x)) 'unquote-splicing))
     ;; (,@expr . rest) → (append expr (expand-qq rest))
     (list 'append (cadr (car x)) (expand-qq (cdr x))))
    (else
     ;; (a . b) → (cons (expand-qq a) (expand-qq b))
     (list 'cons (expand-qq (car x)) (expand-qq (cdr x))))))

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
            (make-cont (list r)
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
                (make-cont (list r)
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
         (make-cont (list r)
           (cps-seq (cdr asts) k)))))))

;; Top-level CPS entry: wrap with %halt continuation
(define (cps-convert ast)
  (let ((r (gensym 'r)))
    (cps ast
      (make-cont (list r)
        (make-prim '%halt (list (make-ref r)))))))

;;; ════════════════════════════════════════════════════════════════════
;;; Datum cache: quoted symbols, strings, and lists get static variables
;;; ════════════════════════════════════════════════════════════════════

(define *datum-cache* '())    ;; ((datum . var-name) ...)
(define *datum-counter* 0)

;; Return the Rust static name for a datum, creating one if needed.
;; Returns a string like "__DATUM_0".
(define (datum-var datum)
  (let ((cached (assoc datum *datum-cache*)))
    (if cached
        (cdr cached)
        (let ((name (string-append "__DATUM_" (number->string *datum-counter*))))
          (set! *datum-counter* (+ *datum-counter* 1))
          (set! *datum-cache* (cons (cons datum name) *datum-cache*))
          name))))

;;; ════════════════════════════════════════════════════════════════════
;;; Lambda collection: walk CPS'd AST, collect all lambdas
;;; ════════════════════════════════════════════════════════════════════

;; Each collected lambda/cont: (id params free-vars body)
(define *lambdas* '())
(define *cont-lambdas* '())  ;; continuation lambdas (defunctionalized separately)
(define *next-id* 0)
(define *globals* '())    ;; known top-level function names
(define *global-ids* '()) ;; ((name . id) ...) for global functions

(define (add-lambda! params body)
  (let ((id *next-id*)
        (free (diff (diff (fv body) (params-all params)) *globals*)))
    (set! *next-id* (+ *next-id* 1))
    (set! *lambdas* (cons (list id params free body) *lambdas*))
    id))

(define (add-cont! params body)
  (let ((id *next-id*)
        (free (diff (diff (fv body) (params-all params)) *globals*)))
    (set! *next-id* (+ *next-id* 1))
    (set! *cont-lambdas* (cons (list id params free body) *cont-lambdas*))
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
       (cond
         ((lam? fn)
          ;; User-lambda administrative redex (let binding): lift body, keep structure
          (make-app (cons (make-lam (lam-params fn) (lift (lam-body fn)))
                          (map lift (app-args ast)))))
         ((cont? fn)
          ;; Cont administrative redex (let binding for CPS temps): lift body, keep structure
          (make-app (cons (make-cont (cont-params fn) (lift (cont-body fn)))
                          (map lift (app-args ast)))))
         (else
          ;; Regular call: lift all parts
          (make-app (map lift (cdr ast)))))))
    ((lam? ast)
     ;; Lambda in value position: lift body, collect, return closure node
     (let* ((body (lift (lam-body ast)))
            (id (add-lambda! (lam-params ast) body))
            (free (diff (diff (fv body) (params-all (lam-params ast))) *globals*)))
       (cons 'closure (cons id free))))
    ((cont? ast)
     ;; Cont in value position: lift body, collect into cont-lambdas, return cont-closure node
     (let* ((body (lift (cont-body ast)))
            (id (add-cont! (cont-params ast) body))
            (free (diff (diff (fv body) (params-all (cont-params ast))) *globals*)))
       (cons 'cont-closure (cons id free))))
    ((seq? ast)
     (make-seq (map lift (seq-exprs ast))))
    (else ast)))

;;; ════════════════════════════════════════════════════════════════════
;;; Rust code emission
;;; ════════════════════════════════════════════════════════════════════

;; Emit a Rust identifier for a global variable (prefixed to avoid collisions)
(define (emit-global-ident name)
  (emit "__g_")
  (rust-ident name))

;; Track which local variables are bound to closure nodes (for letrec patching)
(define *closure-bindings* '())

;; Track current lambda for self-tail-call optimization
(define *current-lambda-id* -1)
(define *current-lambda-params* '())
(define *in-self-loop* #f)

;; Check if a tail-call target resolves to the current lambda
(define (self-call? fn-ast)
  (cond
    ((ref? fn-ast)
     (let ((gid (assq (ref-var fn-ast) *global-ids*)))
       (and gid (= (cdr gid) *current-lambda-id*))))
    ((closure? fn-ast)
     (and (= (closure-id fn-ast) *current-lambda-id*)
          (null? (closure-free fn-ast))))
    (else #f)))

;; Collect all variables that are set! inside an AST (not crossing lambda boundaries)
(define (mutated-vars ast)
  (cond
    ((set? ast) (list (set-var ast)))
    ((app? ast)
     (if (or (lam? (app-fn ast)) (cont? (app-fn ast)))
         (mutated-vars (if (lam? (app-fn ast))
                           (lam-body (app-fn ast))
                           (cont-body (app-fn ast))))
         (union-multi (map mutated-vars (cdr ast)))))
    ((if? ast)  (union (mutated-vars (if-test ast))
                       (union (mutated-vars (if-then ast))
                              (mutated-vars (if-else ast)))))
    ((seq? ast) (union-multi (map mutated-vars (seq-exprs ast))))
    ((lam? ast) '())   ;; don't recurse into nested lambdas
    ((cont? ast) '())
    (else '())))

;; Scan an AST for any self-tail-call (used to decide whether to emit loop)
(define (has-self-tail-call? ast)
  (cond
    ((app? ast)
     (let ((fn (app-fn ast)))
       (if (or (lam? fn) (cont? fn))
           ;; Administrative redex: check body
           (has-self-tail-call? (if (lam? fn) (lam-body fn) (cont-body fn)))
           ;; Real call: check if self-call
           (self-call? fn))))
    ((if? ast)
     (or (has-self-tail-call? (if-then ast))
         (has-self-tail-call? (if-else ast))))
    ((seq? ast)
     (has-self-tail-call? (car (reverse (seq-exprs ast)))))
    (else #f)))

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
         ((char? v)
          (emit "make_char(") (emit (char->integer v)) (emit ")"))
         ((or (symbol? v) (string? v) (pair? v))
          ;; Complex datum → reference a cached static
          (emit "unsafe { ") (emit (datum-var v)) (emit " }"))
         (else (emit "Val::NIL")))))

    ((ref? ast)
     (let ((name (ref-var ast)))
       (let ((gid (assq name *global-ids*)))
         (cond
           (gid
            (emit "make_closure(") (emit (cdr gid)) (emit ", Val::NIL)"))
           ((memq name *globals*)
            (emit "unsafe { ") (emit-global-ident name) (emit " }"))
           (else
            (rust-ident name))))))

    ((set? ast)
     (let ((name (set-var ast)))
       (if (memq name *globals*)
           (begin
             (emit "{ unsafe { ")
             (emit-global-ident name)
             (emit " = ")
             (emit-val (set-val ast))
             (emit "; } Val::NIL }"))
           (let* ((val (set-val ast))
                  ;; Resolve the closure node for this value
                  (closure-node
                    (cond
                      ((closure? val) val)
                      ((ref? val)
                       (let ((binding (assq (ref-var val) *closure-bindings*)))
                         (if binding (cdr binding) #f)))
                      (else #f))))
             (emit "{ ")
             (rust-ident name)
             (emit " = ")
             (emit-val val)
             (emit "; ")
             ;; Register this binding if it's a closure (for future cross-patches)
             (if closure-node
                 (set! *closure-bindings*
                       (cons (cons name closure-node) *closure-bindings*)))
             ;; Letrec patching: after setting 'name', scan ALL known
             ;; closure bindings. Any closure that captured 'name' in its
             ;; free vars has a stale copy — patch it via set_car!.
             (for-each
               (lambda (cb)
                 (let ((closure-var (car cb))
                       (closure-node (cdr cb)))
                   (if (memq name (closure-free closure-node))
                       (let ((pos (list-index name (closure-free closure-node))))
                         (emit "set_car(")
                         (let loop ((d pos))
                           (if (= d 0)
                               (begin (emit "cdr(") (rust-ident closure-var) (emit ")"))
                               (begin (emit "cdr(") (loop (- d 1)) (emit ")"))))
                         (emit ", ") (rust-ident name) (emit "); ")))))
               *closure-bindings*)
             (emit "Val::NIL }")))))

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

    ((cont-closure? ast)
     (let ((id (cont-closure-id ast))
           (free (cont-closure-free ast)))
       (if (null? free)
           (begin (emit "make_cont(") (emit id) (emit ", Val::NIL)"))
           (begin (emit "make_cont(") (emit id) (emit ", ")
                  (emit-env-build free)
                  (emit ")")))))

    ((app? ast)
     ;; (app (lam ...) args) = let binding in value position
     (if (or (lam? (app-fn ast)) (cont? (app-fn ast)))
         (let* ((fn (app-fn ast))
                (params (if (lam? fn) (lam-params fn) (cont-params fn)))
                (body   (if (lam? fn) (lam-body fn)  (cont-body fn))))
           (emit "{ ")
           (emit-let-bindings params (app-args ast))
           (emit-val body)
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
     (emit "; __v != Val::NIL && !__v.is_fixnum() && unsafe { FROM[__v.as_rib()].tag == TAG_PAIR } })"))
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

    ;; Type predicates
    ((eq? op 'symbol?)
     (emit "bool_to_val(!") (emit-val (car args)) (emit ".is_fixnum() && ") (emit-val (car args))
     (emit " != Val::NIL && unsafe { FROM[") (emit-val (car args)) (emit ".as_rib()].tag == TAG_SYM })"))
    ((eq? op 'string?)
     (emit "bool_to_val(is_string(") (emit-val (car args)) (emit "))"))
    ((eq? op 'boolean?)
     (emit "bool_to_val(") (emit-val (car args)) (emit " == TRUE_VAL || ") (emit-val (car args)) (emit " == FALSE_VAL)"))
    ((eq? op 'char?)
     (emit "bool_to_val(is_char(") (emit-val (car args)) (emit "))"))
    ((eq? op 'procedure?)
     (emit "bool_to_val(!") (emit-val (car args)) (emit ".is_fixnum() && ") (emit-val (car args))
     (emit " != Val::NIL && unsafe { FROM[") (emit-val (car args)) (emit ".as_rib()].tag == TAG_CLS })"))
    ((eq? op 'eof-object?)
     (emit "bool_to_val(") (emit-val (car args)) (emit " == EOF_VAL)"))
    ((eq? op 'eqv?)
     (emit "bool_to_val(") (emit-val (car args)) (emit " == ") (emit-val (cadr args)) (emit ")"))
    ((eq? op 'equal?)
     (emit "bool_to_val(scheme_equal(") (emit-val (car args)) (emit ", ") (emit-val (cadr args)) (emit "))"))

    ;; String/symbol ops
    ((eq? op 'string-length)
     (emit "string_length(") (emit-val (car args)) (emit ")"))
    ((eq? op 'string-ref)
     (emit "string_ref(") (emit-val (car args)) (emit ", ") (emit-val (cadr args)) (emit ")"))
    ((eq? op 'string-append)
     (emit-string-append-chain args))
    ((eq? op 'symbol->string)
     (emit "symbol_to_string(") (emit-val (car args)) (emit ")"))
    ((eq? op 'string->symbol)
     (emit "string_to_symbol(") (emit-val (car args)) (emit ")"))
    ((eq? op 'number->string)
     (emit "number_to_string(") (emit-val (car args)) (emit ")"))
    ((eq? op 'string->number)
     (emit "string_to_number(") (emit-val (car args)) (emit ")"))
    ((eq? op 'char->integer)
     (emit "Val::fixnum(char_codepoint(") (emit-val (car args)) (emit "))"))
    ((eq? op 'integer->char)
     (emit "make_char(") (emit-i64 (car args)) (emit ")"))

    ;; List ops
    ((eq? op 'list)
     (emit-list-build args))
    ((eq? op 'length)
     (emit "scheme_length(") (emit-val (car args)) (emit ")"))
    ((eq? op 'append)
     (emit "scheme_append(") (emit-val (car args)) (emit ", ") (emit-val (cadr args)) (emit ")"))
    ((eq? op 'reverse)
     (emit "scheme_reverse(") (emit-val (car args)) (emit ")"))

    ;; I/O
    ((eq? op 'display)
     (emit "{ display(") (emit-val (car args)) (emit "); Val::NIL }"))
    ((eq? op 'newline)
     (emit "{ println!(); Val::NIL }"))
    ((eq? op 'write-char)
     (emit "{ write_char(") (emit-val (car args)) (emit "); Val::NIL }"))
    ((eq? op 'read)
     (emit "scheme_read()"))
    ((eq? op 'error)
     (emit "scheme_error(") (emit-val (car args)) (emit ")"))

    ;; char=?
    ((eq? op 'char=?)
     (emit "bool_to_val(char_codepoint(") (emit-val (car args))
     (emit ") == char_codepoint(") (emit-val (cadr args)) (emit "))"))

    ;; memq — list membership with eq?
    ((eq? op 'memq)
     (emit "scheme_memq(") (emit-val (car args)) (emit ", ") (emit-val (cadr args)) (emit ")"))

    ;; assq/assoc — alist lookup
    ((eq? op 'assq)
     (emit "scheme_assq(") (emit-val (car args)) (emit ", ") (emit-val (cadr args)) (emit ")"))
    ((eq? op 'assoc)
     (emit "scheme_assoc(") (emit-val (car args)) (emit ", ") (emit-val (cadr args)) (emit ")"))

    ;; map / for-each — higher-order, need closure call through trampoline
    ;; These are emitted as runtime functions that use dispatch_cps
    ((eq? op 'map)
     (emit "scheme_map(") (emit-val (car args)) (emit ", ") (emit-val (cadr args)) (emit ")"))
    ((eq? op 'for-each)
     (emit "{ scheme_for_each(") (emit-val (car args)) (emit ", ") (emit-val (cadr args)) (emit "); Val::NIL }"))

    ;; Vectors
    ((eq? op 'make-vector)
     (if (null? (cdr args))
         (begin (emit "make_vector(") (emit-i64 (car args)) (emit ", Val::NIL)"))
         (begin (emit "make_vector(") (emit-i64 (car args)) (emit ", ") (emit-val (cadr args)) (emit ")"))))
    ((eq? op 'vector-ref)
     (emit "vector_ref(") (emit-val (car args)) (emit ", ") (emit-i64 (cadr args)) (emit ")"))
    ((eq? op 'vector-set!)
     (emit "{ vector_set(") (emit-val (car args)) (emit ", ") (emit-i64 (cadr args)) (emit ", ") (emit-val (caddr args)) (emit "); Val::NIL }"))
    ((eq? op 'vector-length)
     (emit "vector_length(") (emit-val (car args)) (emit ")"))
    ((eq? op 'vector?)
     (emit "bool_to_val(is_vector(") (emit-val (car args)) (emit "))"))
    ((eq? op 'vector->list)
     (emit "vector_to_list(") (emit-val (car args)) (emit ")"))
    ((eq? op 'list->vector)
     (emit "list_to_vector(") (emit-val (car args)) (emit ")"))

    ;; %halt — used by CPS as program terminator
    ((eq? op '%halt)
     (emit "{ display(") (emit-val (car args)) (emit "); Val::NIL }"))

    (else
     (emit "Val::NIL /* unknown prim ") (emit op) (emit " */"))))

;; Emit (list a b c) → cons(a, cons(b, cons(c, NIL)))
(define (emit-list-build args)
  (if (null? args)
      (emit "Val::NIL")
      (begin
        (emit "cons(")
        (emit-val (car args))
        (emit ", ")
        (emit-list-build (cdr args))
        (emit ")"))))

;; Emit (string-append a b c ...) → string_append(string_append(a, b), c) ...
(define (emit-string-append-chain args)
  (cond
    ((null? args) (emit "make_string_from_str(\"\")"))
    ((null? (cdr args)) (emit-val (car args)))
    ((null? (cdr (cdr args)))
     (emit "string_append(") (emit-val (car args)) (emit ", ") (emit-val (cadr args)) (emit ")"))
    (else
     (emit "string_append(")
     (emit-string-append-chain (list (car args) (cadr args)))
     (emit ", ")
     (emit-string-append-chain (cdr (cdr args)))
     (emit ")"))))

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

;; Emit set_car! on the closure's environment at position N
;; closure-var is the Rust variable name holding the closure
(define (emit-env-patch closure-var pos)
  ;; Navigate to the right cons cell: cdr(closure) for position 0,
  ;; cdr(cdr(closure)) for position 1, etc.
  (emit "set_car(")
  (let loop ((d pos))
    (if (= d 0)
        (begin (emit "cdr(") (emit closure-var) (emit ")"))
        (begin (emit "cdr(") (loop (- d 1)) (emit ")"))))
  (emit ", ") (emit closure-var) (emit ");"))

;; Emit let bindings for administrative redex
(define (emit-let-bindings params args)
  (if (pair? params)
      (begin
        (emit "let mut ")
        (rust-ident (car params))
        (emit " = ")
        (emit-val (car args))
        (emit "; ")
        ;; Track if this binding is a closure (for letrec patching)
        (if (closure? (car args))
            (set! *closure-bindings*
                  (cons (cons (car params) (car args))
                        *closure-bindings*)))
        (emit-let-bindings (cdr params) (cdr args)))))

;; ── Emit a tail-position expression (returns Action) ──

;; Emit a tail call: all-parts = (fn arg1 arg2 ...)
(define (emit-tail-call all-parts)
  (let ((fn (car all-parts))
        (args (cdr all-parts))
        (nargs (- (length all-parts) 1)))
    ;; Self-tail-call optimization: reassign params and continue
    (if (and *in-self-loop* (self-call? fn))
        (begin
          ;; Evaluate all new arg values into temporaries first
          ;; (to avoid order-of-evaluation issues with shared params)
          (emit "{ ")
          (let loop ((as args) (i 0))
            (if (pair? as)
                (begin
                  (emit "let __t") (emit i) (emit " = ") (emit-val (car as)) (emit "; ")
                  (loop (cdr as) (+ i 1)))))
          ;; Reassign params from temporaries
          (let loop ((ps (params-all *current-lambda-params*)) (i 0))
            (if (pair? ps)
                (begin
                  (rust-ident (car ps)) (emit " = __t") (emit i) (emit "; ")
                  (loop (cdr ps) (+ i 1)))))
          (emit "continue; }"))
        ;; Normal tail call → Action (with return if inside a loop)
        (begin
          (if *in-self-loop* (emit "return "))
          (cond
            ((= nargs 1)
             (emit "Action::Call1(")
             (emit-val fn) (emit ", ") (emit-val (car args)) (emit ")"))
            ((= nargs 2)
             (emit "Action::Call2(")
             (emit-val fn) (emit ", ") (emit-val (car args))
             (emit ", ") (emit-val (cadr args)) (emit ")"))
            ((= nargs 3)
             (emit "Action::Call3(")
             (emit-val fn) (emit ", ") (emit-val (car args))
             (emit ", ") (emit-val (cadr args))
             (emit ", ") (emit-val (caddr args)) (emit ")"))
            (else
             (emit "Action::CallN(")
             (emit-val fn) (emit ", vec![") (emit-val-list args) (emit "])")))))))

(define (emit-tail ast)
  (cond
    ;; Application in tail position
    ((app? ast)
     (let ((fn (app-fn ast)))
       (if (or (lam? fn) (cont? fn))
           ;; Administrative redex (let binding): emit bindings, body in tail
           (let ((params (if (lam? fn) (lam-params fn) (cont-params fn)))
                 (body   (if (lam? fn) (lam-body fn)  (cont-body fn))))
             (emit "{ ")
             (emit-let-bindings params (app-args ast))
             (emit-tail body)
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

    ;; Prim in tail position
    ((prim? ast)
     (cond
       ((eq? (prim-op ast) '%halt)
        (if *in-self-loop* (emit "return "))
        (emit "Action::Halt(") (emit-val (car (prim-args ast))) (emit ")"))
       ((eq? (prim-op ast) 'apply)
        ;; (apply f args-list) in tail position → scheme_apply
        (if *in-self-loop* (emit "return "))
        (emit "scheme_apply(") (emit-val (car (prim-args ast)))
        (emit ", ") (emit-val (cadr (prim-args ast))) (emit ")"))
       (else
        ;; Other prims in tail: wrap result as Halt
        (if *in-self-loop* (emit "return "))
        (emit "Action::Halt(") (emit-prim (prim-op ast) (prim-args ast)) (emit ")"))))

    ;; Lit/ref in tail position: shouldn't happen after CPS
    (else
     (if *in-self-loop* (emit "return "))
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
          (emit "    let mut ")
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
  (set! *closure-bindings* '())  ;; reset per-lambda
  (let* ((id (lambda-id lam))
         (params (lambda-params lam))
         (free (lambda-free lam))
         (body (lambda-body lam))
         (self-call (begin
                      (set! *current-lambda-id* id)
                      (set! *current-lambda-params* params)
                      (has-self-tail-call? body)))
         (mutations (mutated-vars body)))
    (emit "fn __lambda_") (emit id) (emit "(__env: Val")
    ;; Parameters — always mut (set! on params is common; allow_unused_mut suppresses warnings)
    (for-each (lambda (p)
                (emit ", mut ")
                (rust-ident p)
                (emit ": Val"))
              (params-all params))
    (emit ") -> Action {")
    (newline)
    ;; Extract free variables from environment
    (emit-env-extract free)
    ;; Body (in tail position), wrapped in loop if self-calling
    (if self-call
        (begin
          (set! *in-self-loop* #t)
          (emit "    loop { ")
          (emit-tail body)
          (emit " }")
          (set! *in-self-loop* #f))
        (begin
          (emit "    ")
          (emit-tail body)))
    (newline)
    (emit "}")
    (newline)
    (newline)))

;; ── Emit a single cont lambda function ──
;; Cont lambdas always have exactly 1 parameter (the return value).
;; Signature: fn __cont_N(__env: Val, val: Val) -> Action

(define (emit-cont-lambda lam)
  (set! *closure-bindings* '())
  (let* ((id (lambda-id lam))
         (params (lambda-params lam))
         (free (lambda-free lam))
         (body (lambda-body lam)))
    (emit "fn __cont_") (emit id) (emit "(__env: Val, val: Val) -> Action {")
    (newline)
    (emit-env-extract free)
    ;; Bind the single parameter to 'val'
    (emit "    let ")
    (rust-ident (car (params-all params)))
    (emit " = val;")
    (newline)
    (emit "    ")
    (emit-tail body)
    (newline)
    (emit "}")
    (newline)
    (newline)))

;; ── Emit gc_roots_visit (scans all generated static roots) ──
;; Called by cheney_gc to update __g_* and __DATUM_* statics.

(define (emit-gc-roots-visit var-names datum-cache)
  (emit-line "fn gc_roots_visit(visit: &mut impl FnMut(&mut Val)) { unsafe {")
  (for-each (lambda (name)
              (emit "    visit(&mut ")
              (emit-global-ident name)
              (emit-line ");"))
            var-names)
  (for-each (lambda (entry)
              (emit "    visit(&mut ")
              (emit (cdr entry))
              (emit-line ");"))
            datum-cache)
  (emit-line "} }")
  (newline))

;; ── Emit dispatch_cps (user lambdas only) ──

(define (emit-dispatch)
  (emit-line "fn dispatch_cps(closure: Val, args: &[Val]) -> Action {")
  (emit-line "    if is_cont(closure) {")
  (emit-line "        return apply_cont(car(closure).as_fixnum().unwrap(), cdr(closure), args[0]);")
  (emit-line "    }")
  (emit-line "    let code_id = car(closure).as_fixnum().unwrap();")
  (emit-line "    let __env = cdr(closure);")
  (emit-line "    match code_id {")
  ;; Emit each user lambda's dispatch case
  (for-each
    (lambda (lam)
      (let ((id (lambda-id lam))
            (params (lambda-params lam))
            (proper (params-proper (lambda-params lam)))
            (rest (params-rest (lambda-params lam))))
        (emit "        ") (emit id) (emit " => __lambda_") (emit id) (emit "(__env")
        ;; Fixed params
        (let loop ((i 0) (ps proper))
          (if (pair? ps)
              (begin
                (emit ", args[") (emit i) (emit "]")
                (loop (+ i 1) (cdr ps)))))
        ;; Rest param: collect remaining args into a cons-list
        (if rest
            (begin
              (emit ", collect_rest(args, ")
              (emit (length proper))
              (emit ")")))
        (emit "),")
        (newline)))
    (reverse *lambdas*))
  (emit-line "        _ => Action::Halt(Val::NIL),")
  (emit-line "    }")
  (emit-line "}")
  (newline))

;; ── Emit apply_cont (continuation dispatch) ──

(define (emit-apply-cont)
  (emit-line "fn apply_cont(variant: i64, env: Val, val: Val) -> Action {")
  (emit-line "    match variant {")
  (emit-line "        -1 => Action::Halt(val),")
  (for-each
    (lambda (lam)
      (let ((id (lambda-id lam)))
        (emit "        ") (emit id) (emit " => __cont_") (emit id) (emit "(env, val),")
        (newline)))
    (reverse *cont-lambdas*))
  (emit-line "        _ => Action::Halt(Val::NIL),")
  (emit-line "    }")
  (emit-line "}")
  (newline))

;; ── Rust runtime template (static, emitted in one shot) ──

(define runtime-template "// Generated by rsc.scm - CPS + closure conversion pipeline
#![allow(non_snake_case, unused_variables, unused_mut, unused_parens, dead_code, unreachable_code)]

#[derive(Clone, Copy, PartialEq, Eq)]
struct Val(i64);

impl Val {
    const NIL: Val = Val(0);
    #[inline(always)] const fn fixnum(n: i64) -> Val { Val((n << 1) | 1) }
    #[inline(always)] fn is_fixnum(self) -> bool { (self.0 & 1) != 0 }
    #[inline(always)] fn as_fixnum(self) -> Option<i64> { if self.is_fixnum() { Some(self.0 >> 1) } else { None } }
    #[inline(always)] fn as_rib(self) -> usize { (self.0 >> 1) as usize }
}

impl std::fmt::Display for Val {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if let Some(n) = self.as_fixnum() { write!(f, \"{}\", n) }
        else if *self == Val::NIL { write!(f, \"()\") }
        else { write!(f, \"#<rib>\") }
    }
}

const FALSE_VAL: Val = Val(1 << 1);
const TRUE_VAL: Val = Val(2 << 1);
const TAG_PAIR: u8 = 12;
const TAG_CLS: u8 = 14;

#[derive(Clone, Copy)]
struct Rib { car: Val, cdr: Val, tag: u8 }

// Two-space Cheney GC semi-spaces.
// FROM = live allocation space; TO = evacuation target during GC.
// Fixed ribs 0..FIXED_RIBS never move: nil(0), #f(1), #t(2), eof(3), chars(4..260).
static mut FROM: Vec<Rib> = Vec::new();
static mut TO:   Vec<Rib> = Vec::new();
const SPACE_SIZE: usize = 1 << 22;   // 4M ribs ~32 MB per space
const TAG_FWD:    u8     = 253;       // forwarding pointer: car = new Val
const FIXED_RIBS: usize  = 260;       // nil + #f + #t + eof + 256 chars
static mut GC_DEPTH:  usize = 0;       // nested trampoline depth; GC only at depth 0

static mut CHAR_TABLE: [Val; 256] = [Val(0); 256];

fn heap_init() { unsafe {
    FROM = Vec::with_capacity(SPACE_SIZE);
    TO   = Vec::with_capacity(SPACE_SIZE);
    FROM.push(Rib { car: Val::NIL, cdr: Val::NIL, tag: 0 });       // 0: nil
    FROM.push(Rib { car: Val::NIL, cdr: Val::NIL, tag: 0 });       // 1: #f
    FROM.push(Rib { car: Val::NIL, cdr: Val::NIL, tag: 0 });       // 2: #t
    FROM.push(Rib { car: Val::NIL, cdr: Val::NIL, tag: TAG_EOF }); // 3: eof
    // Pre-intern all 256 ASCII chars so eq? works on chars (ribs 4..260)
    for i in 0..256i64 {
        CHAR_TABLE[i as usize] = alloc_rib(Val::fixnum(i), Val::NIL, TAG_CHAR);
    }
}}

#[inline(always)]
fn alloc_rib(car: Val, cdr: Val, tag: u8) -> Val {
    unsafe {
        let idx = FROM.len();
        FROM.push(Rib { car, cdr, tag });
        if GC_BUDGET > 0 { GC_BUDGET -= 1; } // saturate at 0 to signal GC needed
        Val((idx as i64) << 1)
    }
}

#[inline(always)] fn cons(car: Val, cdr: Val) -> Val { alloc_rib(car, cdr, TAG_PAIR) }
#[inline(always)] fn car(v: Val) -> Val { if v.is_fixnum() || v == Val::NIL { Val::NIL } else { unsafe { FROM[v.as_rib()].car } } }
#[inline(always)] fn cdr(v: Val) -> Val { if v.is_fixnum() || v == Val::NIL { Val::NIL } else { unsafe { FROM[v.as_rib()].cdr } } }
#[inline(always)] fn set_car(v: Val, c: Val) { if !v.is_fixnum() && v != Val::NIL { unsafe { FROM[v.as_rib()].car = c; } } }
#[inline(always)] fn set_cdr(v: Val, c: Val) { if !v.is_fixnum() && v != Val::NIL { unsafe { FROM[v.as_rib()].cdr = c; } } }

// --- Cheney GC -------------------------------------------------------

// Copy one rib from FROM to TO, leaving a forwarding pointer in FROM.
// Returns the new Val (index in TO).
fn gc_copy(v: Val) -> Val {
    if v.is_fixnum() { return v; }
    let idx = v.as_rib();
    if idx < FIXED_RIBS { return v; }        // fixed ribs never move
    unsafe {
        if FROM[idx].tag == TAG_FWD {
            return FROM[idx].car;             // already forwarded
        }
        let rib = FROM[idx];
        let new_idx = TO.len();
        TO.push(rib);
        FROM[idx] = Rib { car: Val((new_idx as i64) << 1), cdr: Val::NIL, tag: TAG_FWD };
        Val((new_idx as i64) << 1)
    }
}

// Full Cheney collection.  extra_roots is updated in-place to new locations.
fn cheney_gc(extra_roots: &mut [Val]) {
    unsafe {
        // Seed TO with the fixed ribs at their canonical indices.
        TO.clear();
        for i in 0..FIXED_RIBS { TO.push(FROM[i]); }

        // Evacuate live roots: extra_roots, statics, char table, symbol table.
        for r in extra_roots.iter_mut() { *r = gc_copy(*r); }
        gc_roots_visit(&mut |r: &mut Val| { *r = gc_copy(*r); });
        for ch in CHAR_TABLE.iter_mut() { *ch = gc_copy(*ch); }
        for sym in SYM_TABLE.iter_mut() { *sym = gc_copy(*sym); }

        // Scan: copy car/cdr of every object in TO, handling vectors specially.
        let mut scan = FIXED_RIBS;
        while scan < TO.len() {
            let tag = TO[scan].tag;
            if tag == TAG_VEC {
                // Vector header: car = fixnum(len), cdr = fixnum(old_elem_base).
                let len      = TO[scan].car.as_fixnum().unwrap_or(0) as usize;
                let old_base = TO[scan].cdr.as_fixnum().unwrap_or(0) as usize;
                if len > 0 {
                    let new_base = TO.len();
                    for i in 0..len {
                        let ei = old_base + i;
                        let elem_car = if FROM[ei].tag == TAG_FWD { gc_copy(FROM[ei].car) }
                                       else { gc_copy(FROM[ei].car) };
                        TO.push(Rib { car: elem_car, cdr: Val::NIL, tag: 0 });
                        FROM[ei] = Rib { car: Val(((new_base+i) as i64)<<1), cdr: Val::NIL, tag: TAG_FWD };
                    }
                    TO[scan].cdr = Val::fixnum(new_base as i64);
                }
                // car is fixnum(len), no pointer update needed.
            } else {
                let new_car = gc_copy(TO[scan].car);
                let new_cdr = gc_copy(TO[scan].cdr);
                TO[scan].car = new_car;
                TO[scan].cdr = new_cdr;
            }
            scan += 1;
        }

        // Swap spaces: TO becomes new FROM; FROM becomes empty TO-space.
        std::mem::swap(&mut FROM, &mut TO);
        TO.clear();
        // Reset allocation budget based on remaining free space.
        GC_BUDGET = if FROM.len() < SPACE_SIZE { SPACE_SIZE - FROM.len() } else { 0 };
    }
}


#[inline(always)]
fn make_closure(code_id: i64, __cenv: Val) -> Val { alloc_rib(Val::fixnum(code_id), __cenv, TAG_CLS) }

const TAG_CONT: u8 = 6;
#[inline(always)]
fn make_cont(variant: i64, env: Val) -> Val { alloc_rib(Val::fixnum(variant), env, TAG_CONT) }
#[inline(always)]
fn is_cont(v: Val) -> bool { !v.is_fixnum() && v != Val::NIL && unsafe { FROM[v.as_rib()].tag == TAG_CONT } }

#[inline(always)] fn is_true(v: Val) -> bool { v != FALSE_VAL }
#[inline(always)] fn bool_to_val(b: bool) -> Val { if b { TRUE_VAL } else { FALSE_VAL } }

const TAG_STR: u8 = 4;
const TAG_SYM: u8 = 13;
const TAG_CHAR: u8 = 15;
const TAG_EOF: u8 = 16;
const EOF_VAL: Val = Val(3 << 1); // rib 3

fn make_char(cp: i64) -> Val {
    if cp >= 0 && cp < 256 { unsafe { CHAR_TABLE[cp as usize] } }
    else { alloc_rib(Val::fixnum(cp), Val::NIL, TAG_CHAR) }
}
fn is_char(v: Val) -> bool { !v.is_fixnum() && v != Val::NIL && unsafe { FROM[v.as_rib()].tag == TAG_CHAR } }
fn char_codepoint(v: Val) -> i64 { car(v).as_fixnum().unwrap_or(0) }

fn make_string_from_str(s: &str) -> Val {
    let mut chars = Val::NIL;
    for b in s.bytes().rev() { chars = cons(Val::fixnum(b as i64), chars); }
    alloc_rib(chars, Val::fixnum(s.len() as i64), TAG_STR)
}
fn is_string(v: Val) -> bool { !v.is_fixnum() && v != Val::NIL && unsafe { FROM[v.as_rib()].tag == TAG_STR } }
fn string_length(v: Val) -> Val { cdr(v) }
fn string_ref(s: Val, idx: Val) -> Val {
    let i = idx.as_fixnum().unwrap_or(0);
    let mut c = car(s); let mut n = 0;
    while n < i && c != Val::NIL { c = cdr(c); n += 1; }
    make_char(car(c).as_fixnum().unwrap_or(0))
}
fn string_append(a: Val, b: Val) -> Val {
    let mut chars_a = Vec::new();
    let mut c = car(a); while c != Val::NIL && !c.is_fixnum() { chars_a.push(car(c)); c = cdr(c); }
    let mut chars_b = Vec::new();
    let mut c = car(b); while c != Val::NIL && !c.is_fixnum() { chars_b.push(car(c)); c = cdr(c); }
    let mut __r = Val::NIL;
    for &ch in chars_b.iter().rev() { __r = cons(ch, __r); }
    for &ch in chars_a.iter().rev() { __r = cons(ch, __r); }
    alloc_rib(__r, Val::fixnum((chars_a.len() + chars_b.len()) as i64), TAG_STR)
}
fn number_to_string(n: Val) -> Val {
    let s = format!(\"{}\", n.as_fixnum().unwrap_or(0));
    make_string_from_str(&s)
}
fn string_to_number(s: Val) -> Val {
    let mut bytes = Vec::new();
    let mut c = car(s);
    while c != Val::NIL && !c.is_fixnum() { bytes.push(car(c).as_fixnum().unwrap_or(0) as u8); c = cdr(c); }
    let text = String::from_utf8_lossy(&bytes);
    match text.parse::<i64>() { Ok(n) => Val::fixnum(n), Err(_) => FALSE_VAL }
}

static mut SYM_TABLE: Vec<Val> = Vec::new();
fn intern_symbol(name: &str) -> Val {
    unsafe {
        for &sym in &SYM_TABLE {
            let s = FROM[sym.as_rib()].car;
            if string_eq_str(s, name) { return sym; }
        }
        let s = make_string_from_str(name);
        let sym = alloc_rib(s, Val::NIL, TAG_SYM);
        SYM_TABLE.push(sym);
        sym
    }
}
fn string_eq_str(s: Val, target: &str) -> bool {
    let mut c = car(s); let mut i = 0;
    let bytes = target.as_bytes();
    while c != Val::NIL && !c.is_fixnum() && i < bytes.len() {
        if car(c).as_fixnum().unwrap_or(-1) != bytes[i] as i64 { return false; }
        c = cdr(c); i += 1;
    }
    c == Val::NIL && i == bytes.len()
}
fn symbol_to_string(sym: Val) -> Val { car(sym) }
fn string_to_symbol(s: Val) -> Val {
    // Extract string content and intern
    let mut bytes = Vec::new();
    let mut c = car(s);
    while c != Val::NIL && !c.is_fixnum() { bytes.push(car(c).as_fixnum().unwrap_or(0) as u8); c = cdr(c); }
    let name = String::from_utf8_lossy(&bytes);
    intern_symbol(&name)
}

fn scheme_equal(a: Val, b: Val) -> bool {
    if a == b { return true; }
    if a.is_fixnum() || b.is_fixnum() { return false; }
    if a == Val::NIL || b == Val::NIL { return false; }
    unsafe {
        let ra = &FROM[a.as_rib()]; let rb = &FROM[b.as_rib()];
        if ra.tag != rb.tag { return false; }
        scheme_equal(ra.car, rb.car) && scheme_equal(ra.cdr, rb.cdr)
    }
}

fn display(v: Val) {
    if let Some(n) = v.as_fixnum() { print!(\"{}\", n); }
    else if v == Val::NIL { print!(\"()\"); }
    else if v == TRUE_VAL { print!(\"#t\"); }
    else if v == FALSE_VAL { print!(\"#f\"); }
    else { unsafe {
        let rib = &FROM[v.as_rib()];
        match rib.tag {
            TAG_STR => {
                let mut c = rib.car;
                while c != Val::NIL && !c.is_fixnum() {
                    print!(\"{}\", FROM[c.as_rib()].car.as_fixnum().unwrap_or(0) as u8 as char);
                    c = FROM[c.as_rib()].cdr;
                }
            }
            TAG_SYM => { display(rib.car); }
            TAG_PAIR => {
                print!(\"(\"); display(rib.car);
                let mut rest = rib.cdr;
                while rest != Val::NIL && !rest.is_fixnum() && FROM[rest.as_rib()].tag == TAG_PAIR {
                    print!(\" \"); display(FROM[rest.as_rib()].car);
                    rest = FROM[rest.as_rib()].cdr;
                }
                if rest != Val::NIL { print!(\" . \"); display(rest); }
                print!(\")\");
            }
            TAG_CHAR => { print!(\"{}\", rib.car.as_fixnum().unwrap_or(0) as u8 as char); }
            _ => { print!(\"#<rib>\"); }
        }
    }}
}
fn write_char(v: Val) { let cp = if is_char(v) { char_codepoint(v) } else { v.as_fixnum().unwrap_or(0) }; print!(\"{}\", cp as u8 as char); }

use std::io::Read as IoRead;
static mut INPUT_BUF: Vec<u8> = Vec::new();
static mut INPUT_POS: usize = 0;
fn read_init() { unsafe { std::io::stdin().read_to_end(&mut INPUT_BUF).ok(); } }
fn peek_char() -> i64 { unsafe { if INPUT_POS < INPUT_BUF.len() { INPUT_BUF[INPUT_POS] as i64 } else { -1 } } }
fn read_char_raw() -> i64 { let c = peek_char(); if c >= 0 { unsafe { INPUT_POS += 1; } } c }
fn skip_ws() { loop { let c = peek_char(); if c < 0 { return; } if c == 59 { while peek_char() >= 0 && peek_char() != 10 { read_char_raw(); } } else if c <= 32 { read_char_raw(); } else { return; } } }
fn scheme_read() -> Val {
    skip_ws();
    let c = peek_char();
    if c < 0 { return EOF_VAL; }
    if c == 40 { read_char_raw(); return read_list(); } // (
    if c == 39 { read_char_raw(); let v = scheme_read(); return cons(intern_symbol(\"quote\"), cons(v, Val::NIL)); } // '
    if c == 96 { read_char_raw(); let v = scheme_read(); return cons(intern_symbol(\"quasiquote\"), cons(v, Val::NIL)); } // `
    if c == 44 { read_char_raw(); // ,
        if peek_char() == 64 { read_char_raw(); let v = scheme_read(); return cons(intern_symbol(\"unquote-splicing\"), cons(v, Val::NIL)); } // ,@
        let v = scheme_read(); return cons(intern_symbol(\"unquote\"), cons(v, Val::NIL)); // ,expr
    }
    if c == 34 { return read_string(); } // \"
    if c == 35 { return read_hash(); } // #
    if (c >= 48 && c <= 57) || (c == 45 && { let n = unsafe { if INPUT_POS+1 < INPUT_BUF.len() { INPUT_BUF[INPUT_POS+1] } else { 0 } }; n >= 48 && n <= 57 }) {
        return read_number();
    }
    read_symbol()
}
fn read_list() -> Val {
    skip_ws();
    if peek_char() == 41 { read_char_raw(); return Val::NIL; } // )
    let first = scheme_read();
    skip_ws();
    if peek_char() == 46 { read_char_raw(); let rest = scheme_read(); skip_ws(); read_char_raw(); return cons(first, rest); } // .
    let rest = read_list();
    cons(first, rest)
}
fn read_string() -> Val {
    read_char_raw(); // skip opening \"
    let mut chars = Vec::new();
    loop {
        let c = read_char_raw();
        if c < 0 || c == 34 { break; } // \" or EOF
        if c == 92 { let e = read_char_raw(); chars.push(if e == 110 { 10 } else if e == 116 { 9 } else { e }); } // backslash
        else { chars.push(c); }
    }
    let mut __r = Val::NIL;
    for &ch in chars.iter().rev() { __r = cons(Val::fixnum(ch), __r); }
    alloc_rib(__r, Val::fixnum(chars.len() as i64), TAG_STR)
}
fn read_number() -> Val {
    let mut s = String::new();
    if peek_char() == 45 { s.push('-'); read_char_raw(); }
    while peek_char() >= 48 && peek_char() <= 57 { s.push(read_char_raw() as u8 as char); }
    Val::fixnum(s.parse::<i64>().unwrap_or(0))
}
fn is_delimiter(c: i64) -> bool { c < 0 || c <= 32 || c == 40 || c == 41 || c == 34 || c == 59 }
fn read_symbol() -> Val {
    let mut s = String::new();
    while !is_delimiter(peek_char()) { s.push(read_char_raw() as u8 as char); }
    intern_symbol(&s)
}
fn read_hash() -> Val {
    read_char_raw(); // skip #
    let c2 = peek_char();
    if c2 == 116 { read_char_raw(); return TRUE_VAL; }  // #t
    if c2 == 102 { read_char_raw(); return FALSE_VAL; } // #f
    if c2 == 92 { // #\\
        read_char_raw(); // skip \\
        let c3 = read_char_raw();
        if c3 < 0 { return make_char(0); }
        // Check for named characters
        if (c3 >= 97 && c3 <= 122) || (c3 >= 65 && c3 <= 90) {
            let next = peek_char();
            if next >= 97 && next <= 122 {
                // Multi-char name like newline, space, tab
                let mut name = String::new();
                name.push(c3 as u8 as char);
                while peek_char() >= 97 && peek_char() <= 122 { name.push(read_char_raw() as u8 as char); }
                return match name.as_str() {
                    \"newline\" => make_char(10),
                    \"space\" => make_char(32),
                    \"tab\" => make_char(9),
                    \"return\" => make_char(13),
                    \"nul\" => make_char(0),
                    _ => make_char(name.as_bytes()[0] as i64),
                };
            }
        }
        return make_char(c3);
    }
    // Skip rest of #-prefixed token (e.g. #true, #false)
    while !is_delimiter(peek_char()) { read_char_raw(); }
    if c2 == 116 { TRUE_VAL } else { FALSE_VAL }
}

fn scheme_apply(f: Val, args_list: Val) -> Action {
    let mut args = Vec::new();
    let mut l = args_list;
    while l != Val::NIL && !l.is_fixnum() { args.push(car(l)); l = cdr(l); }
    match args.len() {
        1 => Action::Call1(f, args[0]),
        2 => Action::Call2(f, args[0], args[1]),
        3 => Action::Call3(f, args[0], args[1], args[2]),
        _ => Action::CallN(f, args),
    }
}

fn scheme_length(lst: Val) -> Val { let mut n = 0i64; let mut l = lst; while l != Val::NIL && !l.is_fixnum() { n += 1; l = cdr(l); } Val::fixnum(n) }
fn scheme_append(a: Val, b: Val) -> Val { if a == Val::NIL { b } else { cons(car(a), scheme_append(cdr(a), b)) } }
fn scheme_reverse(lst: Val) -> Val { let mut r = Val::NIL; let mut l = lst; while l != Val::NIL && !l.is_fixnum() { r = cons(car(l), r); l = cdr(l); } r }
fn scheme_error(msg: Val) -> Val { eprint!(\"Error: \"); display(msg); eprintln!(); std::process::exit(1); }

fn scheme_memq(key: Val, lst: Val) -> Val { let mut l = lst; while l != Val::NIL && !l.is_fixnum() { if car(l) == key { return l; } l = cdr(l); } FALSE_VAL }
fn scheme_assq(key: Val, lst: Val) -> Val { let mut l = lst; while l != Val::NIL && !l.is_fixnum() { let p = car(l); if car(p) == key { return p; } l = cdr(l); } FALSE_VAL }
fn scheme_assoc(key: Val, lst: Val) -> Val { let mut l = lst; while l != Val::NIL && !l.is_fixnum() { let p = car(l); if scheme_equal(car(p), key) { return p; } l = cdr(l); } FALSE_VAL }

fn collect_rest(args: &[Val], start: usize) -> Val {
    let mut r = Val::NIL;
    let mut i = args.len();
    while i > start { i -= 1; r = cons(args[i], r); }
    r
}

const TAG_VEC: u8 = 5;
fn is_vector(v: Val) -> bool { !v.is_fixnum() && v != Val::NIL && unsafe { FROM[v.as_rib()].tag == TAG_VEC } }
fn make_vector(len: i64, fill: Val) -> Val {
    let n = len as usize;
    unsafe {
        let hdr = FROM.len();
        FROM.push(Rib { car: Val::fixnum(len), cdr: Val::fixnum((hdr + 1) as i64), tag: TAG_VEC });
        for _ in 0..n { FROM.push(Rib { car: fill, cdr: Val::NIL, tag: 0 }); }
        Val((hdr as i64) << 1)
    }
}
fn vector_ref(v: Val, idx: i64) -> Val {
    let base = cdr(v).as_fixnum().unwrap() as usize;
    unsafe { FROM[base + idx as usize].car }
}
fn vector_set(v: Val, idx: i64, val: Val) {
    let base = cdr(v).as_fixnum().unwrap() as usize;
    unsafe { FROM[base + idx as usize].car = val; }
}
fn vector_length(v: Val) -> Val { car(v) }
fn vector_to_list(v: Val) -> Val {
    let len = car(v).as_fixnum().unwrap();
    let mut r = Val::NIL;
    let mut i = len - 1;
    while i >= 0 { r = cons(vector_ref(v, i), r); i -= 1; }
    r
}
fn list_to_vector(lst: Val) -> Val {
    let len = { let mut n = 0i64; let mut l = lst; while l != Val::NIL && !l.is_fixnum() { n += 1; l = cdr(l); } n };
    let v = make_vector(len, Val::NIL);
    let mut l = lst; let mut i = 0i64;
    while l != Val::NIL && !l.is_fixnum() { vector_set(v, i, car(l)); l = cdr(l); i += 1; }
    v
}

enum Action {
    Call1(Val, Val),
    Call2(Val, Val, Val),
    Call3(Val, Val, Val, Val),
    CallN(Val, Vec<Val>),
    Halt(Val),
}

// Countdown to next GC check.  Decremented in alloc_rib; when it hits zero,
// the trampoline will trigger cheney_gc.  Reset after each collection.
static mut GC_BUDGET: usize = SPACE_SIZE - FIXED_RIBS;

fn trampoline(func: Val, args: &[Val]) -> Val {
    let mut action = dispatch_cps(func, args);
    loop {
        match action {
            Action::Halt(v) => return v,
            Action::Call1(f, a) => {
                action = if unsafe { GC_BUDGET == 0 && GC_DEPTH == 0 } {
                    let mut r = [f, a]; cheney_gc(&mut r); dispatch_cps(r[0], &[r[1]])
                } else { dispatch_cps(f, &[a]) };
            }
            Action::Call2(f, a, b) => {
                action = if unsafe { GC_BUDGET == 0 && GC_DEPTH == 0 } {
                    let mut r = [f, a, b]; cheney_gc(&mut r); dispatch_cps(r[0], &[r[1], r[2]])
                } else { dispatch_cps(f, &[a, b]) };
            }
            Action::Call3(f, a, b, c) => {
                action = if unsafe { GC_BUDGET == 0 && GC_DEPTH == 0 } {
                    let mut r = [f, a, b, c]; cheney_gc(&mut r); dispatch_cps(r[0], &[r[1], r[2], r[3]])
                } else { dispatch_cps(f, &[a, b, c]) };
            }
            Action::CallN(ref f_ref, ref args_ref) => {
                let f = *f_ref; let args = args_ref.clone();
                action = if unsafe { GC_BUDGET == 0 && GC_DEPTH == 0 } {
                    let mut live: Vec<Val> = std::iter::once(f).chain(args.iter().copied()).collect();
                    cheney_gc(&mut live);
                    let mut new_args = args.clone();
                    for (i, a) in new_args.iter_mut().enumerate() { *a = live[i+1]; }
                    dispatch_cps(live[0], &new_args)
                } else { dispatch_cps(f, &args) };
            }
        }
    }
}

fn call_closure_1(f: Val, arg: Val) -> Val {
    let halt = make_cont(-1, Val::NIL);
    unsafe { GC_DEPTH += 1; }
    let r = trampoline(f, &[halt, arg]);
    unsafe { GC_DEPTH -= 1; }
    r
}

fn scheme_map(f: Val, lst: Val) -> Val {
    if lst == Val::NIL { return Val::NIL; }
    let v = call_closure_1(f, car(lst));
    cons(v, scheme_map(f, cdr(lst)))
}
fn scheme_for_each(f: Val, lst: Val) {
    let mut l = lst;
    while l != Val::NIL && !l.is_fixnum() { call_closure_1(f, car(l)); l = cdr(l); }
}

")

(define (emit-runtime) (display runtime-template))


;; Pre-scan an AST to register all complex datums in the cache.
;; Must be called before emission so statics are declared first.
(define (collect-datums ast)
  (cond
    ((lit? ast)
     (let ((v (lit-val ast)))
       (if (or (symbol? v) (string? v) (pair? v))
           (datum-var v)))) ;; force registration
    ((ref? ast) #f)
    ((set? ast) (collect-datums (set-val ast)))
    ((if? ast)
     (collect-datums (if-test ast))
     (collect-datums (if-then ast))
     (collect-datums (if-else ast)))
    ((prim? ast) (for-each collect-datums (prim-args ast)))
    ((app? ast) (for-each collect-datums (cdr ast)))
    ((lam? ast) (collect-datums (lam-body ast)))
    ((cont? ast) (collect-datums (cont-body ast)))
    ((seq? ast) (for-each collect-datums (seq-exprs ast)))
    ((closure? ast) #f)
    ((cont-closure? ast) #f)
    (else #f)))

;; Emit Rust code to construct a datum value (for static initialization)
(define (emit-datum-init datum)
  (cond
    ((symbol? datum)
     (emit "intern_symbol(\"")
     (emit (symbol->string datum))
     (emit "\")"))
    ((string? datum)
     (emit "make_string_from_str(\"")
     ;; Escape special characters
     (let ((s datum))
       (let loop ((i 0))
         (if (< i (string-length s))
             (let ((c (string-ref s i)))
               (cond
                 ((char=? c #\\) (emit "\\\\"))
                 ((char=? c #\") (emit "\\\""))
                 ((char=? c #\newline) (emit "\\n"))
                 ((char=? c #\tab) (emit "\\t"))
                 (else (write-char c)))
               (loop (+ i 1))))))
     (emit "\")"))
    ((number? datum)
     (emit "Val::fixnum(") (emit datum) (emit ")"))
    ((eq? datum #t) (emit "TRUE_VAL"))
    ((eq? datum #f) (emit "FALSE_VAL"))
    ((null? datum) (emit "Val::NIL"))
    ((char? datum)
     (emit "make_char(") (emit (char->integer datum)) (emit ")"))
    ((pair? datum)
     (emit "cons(")
     (emit-datum-init (car datum))
     (emit ", ")
     (emit-datum-init (cdr datum))
     (emit ")"))
    (else (emit "Val::NIL"))))

;;; ════════════════════════════════════════════════════════════════════
;;; Main driver
;;; ════════════════════════════════════════════════════════════════════

(define (define? form) (and (pair? form) (eq? (car form) 'define)))
(define (import? form) (and (pair? form) (eq? (car form) 'import)))
(define (func-define? form)
  (and (define? form) (pair? (cadr form))))  ;; (define (name ...) ...)
(define (var-define? form)
  (and (define? form) (symbol? (cadr form)))) ;; (define name expr)

(define (func-name def) (car (cadr def)))
(define (func-params def) (cdr (cadr def)))
(define (func-body def) (cddr def))

(define (var-name def) (cadr def))
(define (var-init def) (caddr def))

(define (define-syntax? form)
  (and (pair? form) (eq? (car form) 'define-syntax)))

(define (compile-program forms)
  (let* ((func-defs (filter func-define? forms))
         (var-defs (filter var-define? forms))
         (exprs (filter (lambda (x) (and (not (define? x)) (not (import? x)) (not (define-syntax? x)))) forms))
         (func-names (map func-name func-defs))
         (var-names (map var-name var-defs)))

    ;; Reset state
    (set! *lambdas* '())
    (set! *cont-lambdas* '())
    (set! *next-id* 0)
    (set! *gensym-counter* 0)
    (set! *datum-cache* '())
    (set! *datum-counter* 0)
    (set! *globals* (append func-names var-names))
    (set! *global-ids* '())

    ;; CPS + lift each function definition
    (let* ((lifted-funcs
            (map (lambda (def)
                   (let* ((name (func-name def))
                          (params (func-params def))
                          (body-ast (parse-body (func-body def)))
                          (k (gensym 'k))
                          (cps-body (cps body-ast (make-ref k)))
                          (lifted-body (lift cps-body))
                          (id (add-lambda! (cons k params) lifted-body))
                          (free (diff (fv lifted-body) (cons k params))))
                     (set! *global-ids* (cons (cons name id) *global-ids*))
                     (list name id params free)))
                 func-defs))

          ;; Convert variable defines to set! expressions, then append body exprs
          ;; (define x 5) (define y 10) (display x) → (set! x 5) (set! y 10) (display x)
          (all-exprs (append
                       (map (lambda (vd) `(set! ,(var-name vd) ,(var-init vd))) var-defs)
                       exprs))

          ;; CPS + lift top-level expressions (including variable inits)
          (entry-ast
            (if (null? all-exprs)
                (make-prim '%halt (list (make-lit 0)))
                (let* ((body-ast (parse-body all-exprs))
                       (cps-body (cps-convert body-ast))
                       (lifted-body (lift cps-body)))
                  lifted-body))))

      ;; Register entry point as a lambda
      (let ((entry-id (add-lambda! '() entry-ast)))

        ;; Pre-scan all lambda bodies to register datums
        (for-each (lambda (lam) (collect-datums (lambda-body lam)))
                  *lambdas*)
        (for-each (lambda (lam) (collect-datums (lambda-body lam)))
                  *cont-lambdas*)

        ;; Emit everything
        (emit-runtime)

        ;; Emit datum statics
        (for-each (lambda (entry)
                    (emit "static mut ")
                    (emit (cdr entry))
                    (emit-line ": Val = Val::NIL;"))
                  *datum-cache*)
        (if (pair? *datum-cache*) (newline))

        ;; Emit global variable statics
        (for-each (lambda (name)
                    (emit "static mut ")
                    (emit-global-ident name)
                    (emit-line ": Val = Val::NIL;"))
                  var-names)
        (if (pair? var-names) (newline))

        ;; Emit user lambda functions
        (for-each emit-lambda (reverse *lambdas*))

        ;; Emit continuation lambda functions
        (for-each emit-cont-lambda (reverse *cont-lambdas*))

        ;; Emit gc_roots_visit — called by cheney_gc to scan all static roots
        (emit-gc-roots-visit var-names *datum-cache*)

        ;; Emit dispatch + continuation dispatch
        (emit-dispatch)
        (emit-apply-cont)

        ;; Emit main
        (emit-line "fn main() {")
        (emit-line "    heap_init();")
        (emit-line "    read_init();")
        ;; Initialize datum statics
        (for-each (lambda (entry)
                    (emit "    unsafe { ")
                    (emit (cdr entry))
                    (emit " = ")
                    (emit-datum-init (car entry))
                    (emit-line "; }"))
                  *datum-cache*)
        (emit "    let __result = trampoline(make_closure(")
        (emit entry-id)
        (emit-line ", Val::NIL), &[]);")
        (emit-line "    let _ = __result;")
        (emit-line "}")))))

;; Simple filter (in case host Scheme doesn't have it)
(define (filter pred lst)
  (cond ((null? lst) '())
        ((pred (car lst)) (cons (car lst) (filter pred (cdr lst))))
        (else (filter pred (cdr lst)))))

;; Entry point
(compile-program (read-all))
