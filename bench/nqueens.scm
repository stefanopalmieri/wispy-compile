;; N-Queens(8) benchmark
(define (abs-diff a b) (if (> a b) (- a b) (- b a)))

(define (safe? col queens row)
  (if (null? queens) #t
      (let ((qcol (car queens)))
        (if (= col qcol) #f
            (if (= (abs-diff col qcol) (abs-diff row (- row (length queens))))
                #f
                (safe? col (cdr queens) row))))))

(define (nqueens-helper n row queens)
  (if (= row n)
      1
      (let loop ((col 0) (count 0))
        (if (= col n)
            count
            (loop (+ col 1)
                  (if (safe? col queens row)
                      (+ count (nqueens-helper n (+ row 1) (append queens (list col))))
                      count))))))

(define (nqueens n) (nqueens-helper n 0 '()))

(display (nqueens 8))
(newline)
