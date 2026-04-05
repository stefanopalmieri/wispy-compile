;;; fib.scm — Fibonacci (R4RS Scheme)

(define (fib n)
  (if (< n 2)
      n
      (+ (fib (- n 1))
         (fib (- n 2)))))

(define (fib-iter n)
  (define (helper a b count)
    (if (= count 0)
        a
        (helper b (+ a b) (- count 1))))
  (helper 0 1 n))

(display (fib 10))
(newline)
(display (fib-iter 30))
(newline)
