#lang eopl
(require rackunit)

;;; S-list ::= ()
;;;        ::= (Symbol . S-list)
;;;        ::= (S-list . S-list)


(define (filter-in pred lst)
  (cond [(null? lst) '()]
        [(pred (car lst)) (cons (car lst) (filter-in pred (cdr lst)))]
        [else (filter-in pred (cdr lst))]))

(check-equal? (filter-in number? '(a 2 (1 3) b 7)) '(2 7))
(check-equal? (filter-in symbol? '(a (b c) 17 foo)) '(a foo))