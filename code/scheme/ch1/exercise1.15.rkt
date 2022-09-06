#lang eopl
(require rackunit)

(define duple
  (lambda (n x)
    (if (zero? n)
        '()
        (cons x (duple (- n 1) x)))))

;;; test
(check-equal? (duple 2 3) '(3 3))
(check-equal? (duple 4 '(ha ha)) '((ha ha) (ha ha) (ha ha) (ha ha)))
(check-equal? (duple 0 '(blah)) '())

;;; error
(duple 'a '(blah))