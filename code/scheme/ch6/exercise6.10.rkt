#lang eopl
(define list-sum/k
  (lambda (loi k)
    (if (null? loi)
        k
        (list-sum/k (cdr loi)
                    (+ (car loi) k)))))