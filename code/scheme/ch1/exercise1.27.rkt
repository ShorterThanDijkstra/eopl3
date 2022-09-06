#lang eopl
(require rackunit)

;;; S-list ::= ()
;;;        ::= (Symbol . S-list)
;;;        ::= (S-list . S-list)

(define (flatten slist)
  (cond [(null? slist) '()]
        [(symbol? (car slist)) (cons (car slist) (flatten (cdr slist)))]
        [else (append (flatten (car slist)) (flatten (cdr slist)))]))


(check-equal? (flatten '(a b c)) '(a b c))
(check-equal? (flatten '((a) () (b ()) () (c))) '(a b c))
(check-equal? (flatten '((a b) c (((d)) e))) '(a b c d e))
(check-equal? (flatten '(a b (() (c)))) '(a b c))
