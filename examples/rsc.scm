;;; rsc.scm — Self-hosted WispyScheme compiler (Phase 1)
;;;
;;; Compiles a subset of Scheme to standalone Rust binaries.
;;; Phase 1: fixnum arithmetic, if, define, let/let*, named let,
;;;          self-tail-call optimization, display, newline.
;;;
;;; Usage:
;;;   cargo run -- --compile examples/rsc.scm > /tmp/rsc.rs
;;;   rustc -O -o /tmp/rsc /tmp/rsc.rs
;;;   /tmp/rsc < program.scm > program.rs
;;;   rustc -O -o program program.rs && ./program

;;; ════════════════════════════════════════════════════════════════════
;;; Reader: use built-in read, collect all forms until EOF
;;; ════════════════════════════════════════════════════════════════════

(define (read-all)
  (let ((x (read)))
    (if (eof-object? x) '()
        (cons x (read-all)))))

;;; ════════════════════════════════════════════════════════════════════
;;; Utilities
;;; ════════════════════════════════════════════════════════════════════

(define (emit s) (display s))
(define (emit-line s) (display s) (newline))

;; Sanitize a Scheme identifier to a valid Rust identifier.
;; Emits the result directly (avoids list->string which isn't available yet).
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
    (else (write-char c))))

(define (emit-ident-chars s i)
  (if (< i (string-length s))
      (begin (emit-ident-char (string-ref s i))
             (emit-ident-chars s (+ i 1)))))

(define (rust-ident sym)
  (emit-ident-chars (if (symbol? sym) (symbol->string sym) sym) 0))

;; Emit a Rust-safe identifier (avoid Rust keywords)
(define (rust-safe-ident sym)
  (let ((s (symbol->string sym)))
    (cond
      ((equal? s "loop")   (display "loop_"))
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
      (else (rust-ident sym)))))

(define (cadr x) (car (cdr x)))
(define (caddr x) (car (cdr (cdr x))))
(define (cadddr x) (car (cdr (cdr (cdr x)))))
(define (cddr x) (cdr (cdr x)))

;;; ════════════════════════════════════════════════════════════════════
;;; Program analysis: separate defines from expressions
;;; ════════════════════════════════════════════════════════════════════

(define (define? form) (and (pair? form) (eq? (car form) 'define)))

(define (collect-defines forms)
  (if (null? forms) '()
      (if (define? (car forms))
          (cons (car forms) (collect-defines (cdr forms)))
          (collect-defines (cdr forms)))))

(define (collect-exprs forms)
  (if (null? forms) '()
      (if (define? (car forms))
          (collect-exprs (cdr forms))
          (cons (car forms) (collect-exprs (cdr forms))))))

;; Extract function name, params, body from (define (name params...) body...)
(define (func-name def)
  (if (pair? (cadr def))
      (car (cadr def))
      (cadr def)))

(define (func-params def)
  (if (pair? (cadr def))
      (cdr (cadr def))
      '()))

(define (func-body def)
  (if (pair? (cadr def))
      (cddr def)
      (list (caddr def))))

;;; ════════════════════════════════════════════════════════════════════
;;; Self-tail-call detection
;;; ════════════════════════════════════════════════════════════════════

(define (has-self-tail-call? name expr)
  (cond
    ((not (pair? expr)) #f)
    ((eq? (car expr) 'if)
     (or (has-self-tail-call? name (caddr expr))
         (and (pair? (cdr (cddr expr)))
              (has-self-tail-call? name (cadddr expr)))))
    ((eq? (car expr) 'cond)
     (any-clause-has-stc? name (cdr expr)))
    ((eq? (car expr) 'begin)
     (has-self-tail-call-in-begin? name (cdr expr)))
    ((eq? (car expr) 'let)
     (if (symbol? (cadr expr))
         ;; named let — check body
         (has-self-tail-call-in-begin? name (cdr (cddr expr)))
         ;; regular let — check body
         (has-self-tail-call-in-begin? name (cddr expr))))
    ((eq? (car expr) 'let*)
     (has-self-tail-call-in-begin? name (cddr expr)))
    ((and (symbol? (car expr)) (eq? (car expr) name))
     #t)
    (else #f)))

(define (has-self-tail-call-in-begin? name exprs)
  (if (null? exprs) #f
      (if (null? (cdr exprs))
          (has-self-tail-call? name (car exprs))
          (has-self-tail-call-in-begin? name (cdr exprs)))))

(define (any-clause-has-stc? name clauses)
  (if (null? clauses) #f
      (or (has-self-tail-call-in-begin? name (cdr (car clauses)))
          (any-clause-has-stc? name (cdr clauses)))))

;;; ════════════════════════════════════════════════════════════════════
;;; Known functions (for direct call emission)
;;; ════════════════════════════════════════════════════════════════════

(define *functions* '())

(define (known-function? name)
  (define (search fns)
    (if (null? fns) #f
        (if (eq? name (car (car fns))) #t
            (search (cdr fns)))))
  (search *functions*))

;;; ════════════════════════════════════════════════════════════════════
;;; Expression emission: Scheme expr → Rust expression string
;;; ════════════════════════════════════════════════════════════════════

;; Emit a Rust expression for a Scheme expression.
;; tco-name: if non-#f, we're in a TCO loop for this function name.
;; tco-params: the parameter names of the TCO function.
(define (emit-expr expr tco-name tco-params)
  (cond
    ;; Integer literal
    ((number? expr)
     (if tco-name (emit "return "))
     (emit "Val::fixnum(") (emit expr) (emit ")"))

    ;; Boolean
    ((eq? expr #t) (if tco-name (emit "return ")) (emit "TRUE_VAL"))
    ((eq? expr #f) (if tco-name (emit "return ")) (emit "FALSE_VAL"))

    ;; Nil
    ((null? expr) (if tco-name (emit "return ")) (emit "Val::NIL"))

    ;; Symbol (variable reference)
    ((symbol? expr)
     (if tco-name (emit "return "))
     (rust-safe-ident expr))

    ;; Pair (compound expression)
    ((pair? expr)
     (let ((head (car expr)))
       (cond
         ;; (if test then else)
         ((eq? head 'if)
          (emit "if is_true(")
          (emit-expr (cadr expr) #f '())
          (emit ") { ")
          (emit-expr (caddr expr) tco-name tco-params)
          (if (pair? (cdr (cddr expr)))
              (begin (emit " } else { ")
                     (emit-expr (cadddr expr) tco-name tco-params))
              (begin (emit " } else { Val::NIL")))
          (emit " }"))

         ;; (cond clauses...)
         ((eq? head 'cond)
          (emit-cond (cdr expr) tco-name tco-params))

         ;; (begin e1 e2 ...)
         ((eq? head 'begin)
          (emit-begin (cdr expr) tco-name tco-params))

         ;; (let ((var val) ...) body ...) or (let name ((var val) ...) body ...)
         ((eq? head 'let)
          (if (symbol? (cadr expr))
              (emit-named-let expr tco-name tco-params)
              (emit-let (cadr expr) (cddr expr) tco-name tco-params)))

         ;; (let* ((var val) ...) body ...)
         ((eq? head 'let*)
          (emit-let* (cadr expr) (cddr expr) tco-name tco-params))

         ;; (and e1 e2 ...)
         ((eq? head 'and)
          (emit-and (cdr expr)))

         ;; (or e1 e2 ...)
         ((eq? head 'or)
          (emit-or (cdr expr)))

         ;; (not e)
         ((eq? head 'not)
          (if tco-name (emit "return "))
          (emit "bool_to_val(!is_true(")
          (emit-expr (cadr expr) #f '())
          (emit "))"))

         ;; (set! var val)
         ((eq? head 'set!)
          (if tco-name (emit "return "))
          (emit "{ ")
          (rust-safe-ident (cadr expr))
          (emit " = ")
          (emit-expr (caddr expr) #f '())
          (emit "; Val::NIL }"))

         ;; Arithmetic: (+ a b), (- a b), (* a b), (quotient a b), (remainder a b)
         ((and (or (eq? head '+) (eq? head '-) (eq? head '*) (eq? head 'quotient) (eq? head 'remainder) (eq? head 'modulo))
               (pair? (cdr expr)) (pair? (cddr expr)))
          (let ((op (cond ((eq? head '+) "+")
                          ((eq? head '-) "-")
                          ((eq? head '*) "*")
                          ((eq? head 'quotient) "/")
                          ((eq? head 'remainder) "%")
                          ((eq? head 'modulo) "%")
                          (else "+"))))
            (if tco-name (emit "return "))
            (emit "Val::fixnum(")
            (emit-expr (cadr expr) #f '())
            (emit ".as_fixnum().unwrap() ")
            (emit op)
            (emit " ")
            (emit-expr (caddr expr) #f '())
            (emit ".as_fixnum().unwrap())")))

         ;; Unary minus: (- n)
         ((and (eq? head '-) (pair? (cdr expr)) (null? (cddr expr)))
          (if tco-name (emit "return "))
          (emit "Val::fixnum(-")
          (emit-expr (cadr expr) #f '())
          (emit ".as_fixnum().unwrap())"))

         ;; Comparisons: (< a b), (> a b), (= a b), (<= a b), (>= a b)
         ((and (or (eq? head '<) (eq? head '>) (eq? head '=) (eq? head '<=) (eq? head '>=))
               (pair? (cdr expr)) (pair? (cddr expr)))
          (let ((op (cond ((eq? head '<) "<")
                          ((eq? head '>) ">")
                          ((eq? head '=) "==")
                          ((eq? head '<=) "<=")
                          ((eq? head '>=) ">=")
                          (else "=="))))
            (if tco-name (emit "return "))
            (emit "bool_to_val(")
            (emit-expr (cadr expr) #f '())
            (emit ".as_fixnum().unwrap() ")
            (emit op)
            (emit " ")
            (emit-expr (caddr expr) #f '())
            (emit ".as_fixnum().unwrap())")))

         ;; (zero? n)
         ((eq? head 'zero?)
          (if tco-name (emit "return "))
          (emit "bool_to_val(")
          (emit-expr (cadr expr) #f '())
          (emit ".as_fixnum() == Some(0))"))

         ;; (positive? n)
         ((eq? head 'positive?)
          (if tco-name (emit "return "))
          (emit "bool_to_val(")
          (emit-expr (cadr expr) #f '())
          (emit ".as_fixnum().unwrap() > 0)"))

         ;; (negative? n)
         ((eq? head 'negative?)
          (if tco-name (emit "return "))
          (emit "bool_to_val(")
          (emit-expr (cadr expr) #f '())
          (emit ".as_fixnum().unwrap() < 0)"))

         ;; (number? x)
         ((eq? head 'number?)
          (if tco-name (emit "return "))
          (emit "bool_to_val(")
          (emit-expr (cadr expr) #f '())
          (emit ".is_fixnum())"))

         ;; (eq? a b)
         ((eq? head 'eq?)
          (if tco-name (emit "return "))
          (emit "bool_to_val(")
          (emit-expr (cadr expr) #f '())
          (emit " == ")
          (emit-expr (caddr expr) #f '())
          (emit ")"))

         ;; (display x)
         ((eq? head 'display)
          (if tco-name (emit "return "))
          (emit "{ let __dv = ")
          (emit-expr (cadr expr) #f '())
          (emit "; print!(\"{}\", __dv.as_fixnum().unwrap()); Val::NIL }"))

         ;; (newline)
         ((eq? head 'newline)
          (if tco-name (emit "return "))
          (emit "{ println!(); Val::NIL }"))

         ;; Self-tail-call in TCO context
         ((and tco-name (eq? head tco-name))
          (emit-tco-call tco-params (cdr expr) tco-name))

         ;; display / newline in TCO context
         ((and tco-name (eq? head 'display))
          (emit "{ let __dv = ")
          (emit-expr (cadr expr) #f '())
          (emit "; print!(\"{}\", __dv.as_fixnum().unwrap()); return Val::NIL }"))

         ((and tco-name (eq? head 'newline))
          (emit "{ println!(); return Val::NIL }"))

         ;; Known function call
         ((and (symbol? head) (known-function? head))
          (if tco-name (emit "return "))
          (rust-safe-ident head)
          (emit "(")
          (emit-args (cdr expr))
          (emit ")"))

         ;; Unknown call — error for Phase 1
         (else
          (if tco-name (emit "return "))
          (emit "Val::NIL /* unknown call: ")
          (emit (if (symbol? head) (symbol->string head) "?"))
          (emit " */")))))

    ;; Fallback
    (else (emit "Val::NIL"))))

;; Emit comma-separated arguments
(define (emit-args args)
  (if (pair? args)
      (begin
        (emit-expr (car args) #f '())
        (if (pair? (cdr args))
            (begin (emit ", ") (emit-args (cdr args)))
            #f))
      #f))

;; Emit TCO self-tail-call: assign to temps, then to params, continue
(define (emit-tco-temps ps xs i)
  (if (pair? ps)
      (begin
        (emit "let __t") (emit i) (emit " = ")
        (emit-expr (car xs) #f '())
        (emit "; ")
        (emit-tco-temps (cdr ps) (cdr xs) (+ i 1)))))

(define (emit-tco-assigns ps i)
  (if (pair? ps)
      (begin
        (rust-safe-ident (car ps))
        (emit " = __t") (emit i) (emit "; ")
        (emit-tco-assigns (cdr ps) (+ i 1)))))

(define (emit-tco-call params args tco-name)
  (emit "{ ")
  (emit-tco-temps params args 0)
  (emit-tco-assigns params 0)
  (emit "continue; }"))

;; Emit begin block
(define (emit-begin-rest es tco-name tco-params)
  (if (null? (cdr es))
      (emit-expr (car es) tco-name tco-params)
      (begin
        (emit-expr (car es) #f '())
        (emit "; ")
        (emit-begin-rest (cdr es) tco-name tco-params))))

(define (emit-begin exprs tco-name tco-params)
  (if (null? exprs) (emit "Val::NIL")
      (if (null? (cdr exprs))
          (emit-expr (car exprs) tco-name tco-params)
          (begin
            (emit "{ ")
            (emit-begin-rest exprs tco-name tco-params)
            (emit " }")))))

;; Emit let bindings
(define (emit-let-bindings bs)
  (if (pair? bs)
      (let ((b (car bs)))
        (emit "let ")
        (rust-safe-ident (car b))
        (emit " = ")
        (emit-expr (cadr b) #f '())
        (emit "; ")
        (emit-let-bindings (cdr bs)))))

(define (emit-let bindings body tco-name tco-params)
  (emit "{ ")
  (emit-let-bindings bindings)
  (emit-begin body tco-name tco-params)
  (emit " }"))

;; Emit let* bindings (same as let for Phase 1 — no mutual refs)
(define (emit-let* bindings body tco-name tco-params)
  (emit-let bindings body tco-name tco-params))

;; Emit named let: (let name ((var val) ...) body...)
(define (emit-named-let-bindings bs)
  (if (pair? bs)
      (let ((b (car bs)))
        (emit "let mut ")
        (rust-safe-ident (car b))
        (emit " = ")
        (emit-expr (cadr b) #f '())
        (emit "; ")
        (emit-named-let-bindings (cdr bs)))))

(define (emit-named-let expr tco-name tco-params)
  (let ((loop-name (cadr expr))
        (bindings (caddr expr))
        (body (cdr (cddr expr))))
    (emit "{ ")
    (emit-named-let-bindings bindings)
    (emit "loop { ")
    (let ((params (map car bindings)))
      (emit-begin body loop-name params))
    (emit " } }")))

;; Emit cond
(define (emit-cond clauses tco-name tco-params)
  (if (null? clauses) (emit "Val::NIL")
      (let ((clause (car clauses)))
        (if (eq? (car clause) 'else)
            (begin (emit "{ ")
                   (emit-begin (cdr clause) tco-name tco-params)
                   (emit " }"))
            (begin
              (emit "if is_true(")
              (emit-expr (car clause) #f '())
              (emit ") { ")
              (emit-begin (cdr clause) tco-name tco-params)
              (if (pair? (cdr clauses))
                  (begin (emit " } else { ")
                         (emit-cond (cdr clauses) tco-name tco-params)
                         (emit " }"))
                  (emit " } else { Val::NIL }")))))))

;; Emit and
(define (emit-and exprs)
  (if (null? exprs) (emit "TRUE_VAL")
      (if (null? (cdr exprs))
          (emit-expr (car exprs) #f '())
          (begin
            (emit "{ let __av = ")
            (emit-expr (car exprs) #f '())
            (emit "; if !is_true(__av) { __av } else { ")
            (emit-and (cdr exprs))
            (emit " } }")))))

;; Emit or
(define (emit-or exprs)
  (if (null? exprs) (emit "FALSE_VAL")
      (if (null? (cdr exprs))
          (emit-expr (car exprs) #f '())
          (begin
            (emit "{ let __ov = ")
            (emit-expr (car exprs) #f '())
            (emit "; if is_true(__ov) { __ov } else { ")
            (emit-or (cdr exprs))
            (emit " } }")))))

;;; ════════════════════════════════════════════════════════════════════
;;; Function emission
;;; ════════════════════════════════════════════════════════════════════

(define (emit-func-params ps needs-tco first)
  (if (pair? ps)
      (begin
        (if (not first) (emit ", "))
        (if needs-tco (emit "mut "))
        (rust-safe-ident (car ps))
        (emit ": Val")
        (emit-func-params (cdr ps) needs-tco #f))))

(define (emit-function def)
  (let* ((name (func-name def))
         (params (func-params def))
         (body (func-body def))
         (needs-tco (has-self-tail-call? name (if (null? (cdr body)) (car body) (cons 'begin body)))))
    (emit "fn ")
    (rust-safe-ident name)
    (emit "(")
    ;; Parameters
    (emit-func-params params needs-tco #t)
    (emit ") -> Val {")
    (newline)
    (emit "    ")
    (if needs-tco
        ;; TCO: wrap in loop
        (begin
          (emit "loop { ")
          (emit-begin body name params)
          (emit " }"))
        ;; No TCO: just emit body
        (emit-begin body #f '()))
    (newline)
    (emit "}")
    (newline)
    (newline)))

;;; ════════════════════════════════════════════════════════════════════
;;; Runtime emission (minimal Phase 1 — fixnum only)
;;; ════════════════════════════════════════════════════════════════════

(define (emit-runtime)
  (emit-line "// Generated by rsc.scm — self-hosted WispyScheme compiler")
  (emit-line "#![allow(non_snake_case, unused_variables, unused_mut, unused_parens, dead_code, unreachable_code)]")
  (newline)
  (emit-line "#[derive(Clone, Copy, PartialEq, Eq)]")
  (emit-line "struct Val(i64);")
  (newline)
  (emit-line "impl Val {")
  (emit-line "    const NIL: Val = Val(0);")
  (emit-line "    #[inline(always)]")
  (emit-line "    const fn fixnum(n: i64) -> Val { Val((n << 1) | 1) }")
  (emit-line "    #[inline(always)]")
  (emit-line "    fn is_fixnum(self) -> bool { (self.0 & 1) != 0 }")
  (emit-line "    #[inline(always)]")
  (emit-line "    fn as_fixnum(self) -> Option<i64> {")
  (emit-line "        if self.is_fixnum() { Some(self.0 >> 1) } else { None }")
  (emit-line "    }")
  (emit-line "}")
  (newline)
  (emit-line "const FALSE_VAL: Val = Val(1 << 1);")
  (emit-line "const TRUE_VAL: Val = Val(2 << 1);")
  (newline)
  (emit-line "#[inline(always)]")
  (emit-line "fn is_true(v: Val) -> bool { v != FALSE_VAL }")
  (newline)
  (emit-line "#[inline(always)]")
  (emit-line "fn bool_to_val(b: bool) -> Val { if b { TRUE_VAL } else { FALSE_VAL } }")
  (newline))

;;; ════════════════════════════════════════════════════════════════════
;;; Main driver
;;; ════════════════════════════════════════════════════════════════════

(define (compile-program forms)
  (let ((defines (collect-defines forms))
        (exprs (collect-exprs forms)))
    ;; Register all functions
    (set! *functions*
      (map (lambda (d)
             (list (func-name d) (func-params d)))
           defines))
    ;; Emit
    (emit-runtime)
    ;; Emit functions
    (for-each emit-function defines)
    ;; Emit main
    (emit-line "fn main() {")
    (for-each (lambda (e)
                (emit "    { let _ = ")
                (emit-expr e #f '())
                (emit-line "; }"))
              exprs)
    (emit-line "}")))

;; Entry point
(compile-program (read-all))
