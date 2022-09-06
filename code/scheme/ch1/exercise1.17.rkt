#lang eopl
(require rackunit)

(define down
  (lambda (lst)
    (if (null? lst)
        '()
        (cons (cons (car lst) '())
              (down (cdr lst))))))

(check-equal? (down '(1 2 3)) '((1) (2) (3)))
(check-equal? (down '((a) (fine) (idea))) '(((a)) ((fine)) ((idea))))
(check-equal? (down '(a (more (complicated)) object)) '((a) ((more (complicated))) (object)))
