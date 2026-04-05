;;; r4rs-smoke.scm — Basic R4RS compliance smoke tests

;; Booleans
(display (not #f))        ; #t
(display (not 0))         ; #f
(display (boolean? #t))   ; #t
(display (boolean? 42))   ; #f
(newline)

;; Pairs and lists
(display (cons 1 2))          ; (1 . 2)
(display (car (cons 1 2)))    ; 1
(display (cdr (cons 1 2)))    ; 2
(display (pair? (cons 1 2)))  ; #t
(display (pair? 42))          ; #f
(display (null? '()))         ; #t
(display (list 1 2 3))        ; (1 2 3)
(display (length '(1 2 3)))   ; 3
(newline)

;; Symbols
(display (symbol? 'foo))           ; #t
(display (symbol? 42))             ; #f
(display (symbol->string 'hello))  ; "hello"
(newline)

;; Numbers
(display (+ 3 4))            ; 7
(display (- 10 3))           ; 7
(display (* 6 7))            ; 42
(display (quotient 10 3))    ; 3
(display (remainder 10 3))   ; 1
(display (modulo 10 3))      ; 1
(display (= 7 7))            ; #t
(display (< 3 5))            ; #t
(display (zero? 0))          ; #t
(display (even? 4))          ; #t
(display (odd? 3))           ; #t
(display (max 3 5 1))        ; 5
(display (min 3 5 1))        ; 1
(display (abs -7))           ; 7
(display (gcd 12 8))         ; 4
(newline)

;; Characters
(display (char? #\a))              ; #t
(display (char-alphabetic? #\a))   ; #t
(display (char->integer #\A))      ; 65
(display (integer->char 65))       ; A
(newline)

;; Strings
(display (string? "hello"))        ; #t
(display (string-length "hello"))  ; 5
(display (string-ref "hello" 0))   ; h
(display (substring "hello" 1 3))  ; "el"
(display (string-append "he" "llo")) ; "hello"
(newline)

;; Vectors
(display (vector 1 2 3))          ; #(1 2 3)
(display (vector-ref #(1 2 3) 1)) ; 2
(display (vector-length #(1 2 3))); 3
(newline)

;; Control
(display (apply + '(1 2 3)))      ; 6
(display (map car '((1 2) (3 4) (5 6))))  ; (1 3 5)
(newline)

;; Lambda and closures
(display ((lambda (x y) (+ x y)) 3 4))  ; 7
(define (make-adder n)
  (lambda (x) (+ x n)))
(display ((make-adder 10) 32))    ; 42
(newline)

;; call/cc
(display (call-with-current-continuation
           (lambda (k) (+ 1 (k 42)))))  ; 42
(newline)

;; Tail recursion
(define (loop n)
  (if (= n 0) 'done
      (loop (- n 1))))
(display (loop 1000000))  ; done (must not stack overflow)
(newline)

(display "All smoke tests passed.")
(newline)
