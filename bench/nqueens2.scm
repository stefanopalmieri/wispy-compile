;; N-Queens(8) benchmark — no named let
(define (abs-diff a b) (if (> a b) (- a b) (- b a)))

(define (safe? col queens row)
  (if (null? queens) #t
      (let ((qcol (car queens)))
        (if (= col qcol) #f
            (if (= (abs-diff col qcol) (abs-diff row (- row (length queens))))
                #f
                (safe? col (cdr queens) row))))))

(define (count-cols n col row queens)
  (if (= col n)
      0
      (+ (if (safe? col queens row)
             (nqueens-helper n (+ row 1) (append queens (list col)))
             0)
         (count-cols n (+ col 1) row queens))))

(define (nqueens-helper n row queens)
  (if (= row n)
      1
      (count-cols n 0 row queens)))

(define (nqueens n) (nqueens-helper n 0 '()))

(display (nqueens 8))
(newline)
