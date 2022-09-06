#lang eopl
(require rackunit)

(define (every? pred lst)
  (cond [(null? lst) #t]
        [(pred (car lst)) (every? pred (cdr lst))]
        [else #f]))

(check-equal? (every? number? '(a b c 3 e)) #f)
(check-equal? (every? number? '(1 2 3 5 4)) #t)
(check-equal? (every? number? '(1 2 3 a 5 4)) #f)
