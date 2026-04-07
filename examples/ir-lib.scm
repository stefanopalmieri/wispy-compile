;;; ir-lib.scm — Shared expression IR for the self-hosted tools
;;;
;;; A 7-node tagged-pair encoding for algebraic expressions.
;;; Used by the specializer, Futamura projections, and transpiler.
;;;
;;; Expression encoding:
;;;   Atom(n)           -> (0 . n)           constant (algebra element index)
;;;   Var(name)         -> (1 . name)        variable (a Scheme symbol)
;;;   Dot(a, b)         -> (2 . (a . b))     Cayley table application
;;;   If(test, t, e)    -> (3 . (test . (t . e)))   conditional
;;;   Let(x, val, body) -> (4 . (x . (val . body))) binding
;;;   Lam(x, body)      -> (5 . (x . body))  abstraction
;;;   App(fn, arg)      -> (6 . (fn . arg))  application
;;;
;;; Tags are integers 0-6, NOT algebra elements. This avoids
;;; confusion between IR tags and the values being manipulated.

;;; ── Constructors ───────────────────────────────────────────────────

(define (mk-atom n)          (cons 0 n))
(define (mk-var name)        (cons 1 name))
(define (mk-dot a b)         (cons 2 (cons a b)))
(define (mk-if test t e)     (cons 3 (cons test (cons t e))))
(define (mk-let x val body)  (cons 4 (cons x (cons val body))))
(define (mk-lam x body)      (cons 5 (cons x body)))
(define (mk-app fn arg)      (cons 6 (cons fn arg)))

;;; ── Tag and payload ────────────────────────────────────────────────

(define (expr-tag e)     (car e))
(define (expr-payload e) (cdr e))

;;; ── Predicates ─────────────────────────────────────────────────────

(define (is-atom? e) (= (expr-tag e) 0))
(define (is-var? e)  (= (expr-tag e) 1))
(define (is-dot? e)  (= (expr-tag e) 2))
(define (is-if? e)   (= (expr-tag e) 3))
(define (is-let? e)  (= (expr-tag e) 4))
(define (is-lam? e)  (= (expr-tag e) 5))
(define (is-app? e)  (= (expr-tag e) 6))

;;; ── Accessors ──────────────────────────────────────────────────────

;; Atom: payload = n
(define (atom-val e) (cdr e))

;; Var: payload = name (symbol)
(define (var-name e) (cdr e))

;; Dot(a, b): payload = (a . b)
(define (dot-a e) (car (cdr e)))
(define (dot-b e) (cdr (cdr e)))

;; If(test, t, e): payload = (test . (t . e))
(define (if-test e) (car (cdr e)))
(define (if-then e) (car (cdr (cdr e))))
(define (if-else e) (cdr (cdr (cdr e))))

;; Let(x, val, body): payload = (x . (val . body))
(define (let-var e)  (car (cdr e)))
(define (let-val e)  (car (cdr (cdr e))))
(define (let-body e) (cdr (cdr (cdr e))))

;; Lam(x, body): payload = (x . body)
(define (lam-var e)  (car (cdr e)))
(define (lam-body e) (cdr (cdr e)))

;; App(fn, arg): payload = (fn . arg)
(define (app-fn e)  (car (cdr e)))
(define (app-arg e) (cdr (cdr e)))

;;; ── Substitution ───────────────────────────────────────────────────
;;; Replace all free occurrences of variable `var` with `val` in `expr`.
;;; Respects shadowing in let and lam.

(define (subst-expr var val expr)
  (cond
    ((is-atom? expr) expr)
    ((is-var? expr)
     (if (eq? (var-name expr) var) val expr))
    ((is-dot? expr)
     (mk-dot (subst-expr var val (dot-a expr))
             (subst-expr var val (dot-b expr))))
    ((is-if? expr)
     (mk-if (subst-expr var val (if-test expr))
            (subst-expr var val (if-then expr))
            (subst-expr var val (if-else expr))))
    ((is-let? expr)
     (if (eq? (let-var expr) var)
         ;; Shadowed: substitute in val only, not body
         (mk-let (let-var expr)
                 (subst-expr var val (let-val expr))
                 (let-body expr))
         (mk-let (let-var expr)
                 (subst-expr var val (let-val expr))
                 (subst-expr var val (let-body expr)))))
    ((is-lam? expr)
     (if (eq? (lam-var expr) var)
         expr  ;; Shadowed
         (mk-lam (lam-var expr)
                 (subst-expr var val (lam-body expr)))))
    ((is-app? expr)
     (mk-app (subst-expr var val (app-fn expr))
             (subst-expr var val (app-arg expr))))
    (else expr)))

;;; ── Pretty-printer ─────────────────────────────────────────────────
;;; Prints IR expressions in a readable form.

(define (ir-display expr)
  (cond
    ((is-atom? expr)
     (display (atom-val expr)))
    ((is-var? expr)
     (display (var-name expr)))
    ((is-dot? expr)
     (display "(dot ")
     (ir-display (dot-a expr))
     (display " ")
     (ir-display (dot-b expr))
     (display ")"))
    ((is-if? expr)
     (display "(if ")
     (ir-display (if-test expr))
     (display " ")
     (ir-display (if-then expr))
     (display " ")
     (ir-display (if-else expr))
     (display ")"))
    ((is-let? expr)
     (display "(let ")
     (display (let-var expr))
     (display " ")
     (ir-display (let-val expr))
     (display " ")
     (ir-display (let-body expr))
     (display ")"))
    ((is-lam? expr)
     (display "(lam ")
     (display (lam-var expr))
     (display " ")
     (ir-display (lam-body expr))
     (display ")"))
    ((is-app? expr)
     (display "(app ")
     (ir-display (app-fn expr))
     (display " ")
     (ir-display (app-arg expr))
     (display ")"))
    (else
     (display "??"))))
