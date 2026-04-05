;;; nqueens.scm — N-Queens solver (R4RS Scheme)

(define (abs-diff a b)
  (if (> a b) (- a b) (- b a)))

(define (safe? queen dist placed)
  (if (null? placed) #t
      (let ((q (car placed)))
        (cond ((= queen q) #f)
              ((= (abs-diff queen q) dist) #f)
              (else (safe? queen (+ dist 1) (cdr placed)))))))

(define (nqueens-count n row placed)
  (if (= row n)
      1
      (count-cols n 0 row placed)))

(define (count-cols n col row placed)
  (if (= col n)
      0
      (+ (if (safe? col 1 placed)
             (nqueens-count n (+ row 1) (cons col placed))
             0)
         (count-cols n (+ col 1) row placed))))

(define (nqueens n)
  (nqueens-count n 0 '()))

(display (nqueens 8))
(newline)
