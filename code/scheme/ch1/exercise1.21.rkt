#lang eopl
(require rackunit)

(define product
  (lambda (sos1 sos2)
    (if (or (null? sos1) (null? sos2))
        '()
        (append (multiple (car sos1) sos2)
                (product (cdr sos1) sos2)))))

(define multiple
  (lambda (s sos)
    (if (null? sos) '()
        (cons (list s (car sos)) (multiple s (cdr sos))))))


(check-equal? (product '(a b c) '(x y))
              '((a x) (a y) (b x) (b y) (c x) (c y)))