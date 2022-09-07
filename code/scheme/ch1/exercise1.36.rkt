#lang eopl
(require rackunit)
(define (g first rest)
  (cons first
        (map (lambda (pair) (list (+ (car pair) 1) (cadr pair)))
             rest)))


(define number-elements
  (lambda (lst)
    (if (null? lst) '()
        (g (list 0 (car lst)) (number-elements (cdr lst))))))

;;; test
(check-equal? (number-elements '(a b c d e))
              '((0 a) (1 b) (2 c) (3 d) (4 e)))