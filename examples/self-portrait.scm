;; self-portrait.scm
;;
;; The language draws a picture of its own brain.
;; The Cayley table rendered by the algebra it encodes.

;; Element names: core (0-11), type tags (12-19), specials (20-22)
(define *names*
  (list "." "X" "Q" "E" "f" "h" "g" "p" "A" "C" "t" "Y"
        "Pa" "Sy" "Cl" "St" "Ve" "Ch" "Co" "Po"
        "#t" "Ef" "Vd"))

(define (element-name i)
  (if (< i (length *names*))
      (list-ref *names* i)
      (number->string i)))

;; Pad a string to width with trailing spaces
(define (pad s width)
  (let loop ((s s))
    (if (>= (string-length s) width)
        s
        (loop (string-append s " ")))))

;; Header
(define (print-header n)
  (display (pad "" 4))
  (do ((j 0 (+ j 1))) ((= j n))
    (display (pad (element-name j) 4)))
  (newline)
  ;; Separator
  (display (pad "" 4))
  (do ((j 0 (+ j 1))) ((= j n))
    (display "----"))
  (newline))

;; One row
(define (print-row i n)
  (display (pad (element-name i) 4))
  (do ((j 0 (+ j 1))) ((= j n))
    (let ((val (dot i j)))
      (display (pad (element-name val) 4))))
  (newline))

;; The full table: 23 active elements (0-22)
(define (self-portrait)
  (let ((n 23))
    (newline)
    (display "  The Cayley Table of WispyScheme")
    (newline)
    (display "  32x32 algebra, 1KB — rendered by itself")
    (newline)
    (newline)
    (print-header n)
    (do ((i 0 (+ i 1))) ((= i n))
      (print-row i n))
    (newline)
    (display "  . = TOP (nil)    X = BOT (#f/error)")
    (newline)
    (display "  f = CAR  h = CDR  g = CONS  p = RHO  t = TAU")
    (newline)
    (display "  Q/E = retraction pair  Y = fixed point  A = APPLY  C = call/cc")
    (newline)
    (newline)))

(self-portrait)
