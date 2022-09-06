#lang eopl
(require rackunit)

(define invert
  (lambda (lst)
    (if (null? lst)
        '()
        (cons (invert-pair (car lst))
              (invert (cdr lst))))))

(define invert-pair
  (lambda (pair)
    (cons (cadr pair)
          (cons (car pair) '()))))

(check-equal?  (invert '((a 1) (a 2) (1 b) (2 b)))
               '((1 a) (2 a) (b 1) (b 2)))