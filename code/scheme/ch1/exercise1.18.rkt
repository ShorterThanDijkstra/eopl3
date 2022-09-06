#lang eopl
(require rackunit)

;;; S-list ::= ()
;;;        ::= (S-exp . S-list)
;;; S-exp  ::= Symbol | S-list
;;; =>
;;; S-list ::= ()
;;;        ::= (Symbol . S-list)
;;;        ::= (S-list . S-list)

(define swapper
  (lambda (s1 s2 slist)
    (if (null? slist) '()
        (let [(first (car slist)) (rest (cdr slist))]
          (if (symbol? first)
              (cond [(eqv? first s1) (cons s2 (swapper s1 s2 rest))]
                    [(eqv? first s2) (cons s1 (swapper s1 s2 rest))]
                    [else (cons first (swapper s1 s2 rest))])
              (cons (swapper s1 s2 first)
                    (swapper s1 s2 rest)))))))

(check-equal?  (swapper 'a 'd '(a b c d)) '(d b c a))
(check-equal?  (swapper 'a 'd '(a d () c d)) '(d a () c a))
(check-equal?  (swapper 'x 'y '((x) y (z (x)))) '((y) x (z (y))))
