#lang eopl
(require rackunit)

(define (exists? pred lst)
  (cond [(null? lst) #f]
        [(pred (car lst)) #t]
        [else (exists? pred (cdr lst))]))


(check-equal? (exists? number? '(a b c 3 e)) #t)
(check-equal? (exists? number? '(a b c d e)) #f)
