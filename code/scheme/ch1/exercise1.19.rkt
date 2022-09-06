#lang eopl
(require rackunit)

(define list-set-with-index
  (lambda (lst n x i)
    (cond [(null? lst) '()]
          [(eqv? n i) (cons x (cdr lst))]
          [else (cons (car lst)
                      (list-set-with-index (cdr lst) n x (+ 1 i)))])))
(define list-set
  (lambda (lst n x)
    (list-set-with-index lst n x 0)))

(check-equal? (list-set '(a b c d) 2 '(1 2)) '(a b (1 2) d))
(check-equal? (list-ref (list-set '(a b c d) 3 '(1 5 10)) 3)  '(1 5 10))
