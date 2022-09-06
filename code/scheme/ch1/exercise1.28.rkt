#lang eopl
(require rackunit)

(define (merge loi1 loi2)
  (cond [(null? loi1) loi2]
        [(null? loi2) loi1]
        [else (let [(i1 (car loi1)) (i2 (car loi2))]
                (if (< i1 i2) (cons i1 (merge (cdr loi1) loi2))
                    (cons i2 (merge loi1 (cdr loi2)))))]))

(check-equal? (merge '(1 4) '(1 2 8)) '(1 1 2 4 8))
(check-equal? (merge '(35 62 81 90 91)  '(3 83 85 90)) '(3 35 62 81 83 85 90 90 91))
