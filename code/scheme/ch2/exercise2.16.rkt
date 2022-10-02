#lang eopl
(require rackunit)

; Lc-exp ::= Identifier
;        ::= (lambda Identifier Lc-exp)
;        ::= (Lc-exp Lc-exp)


(define lambda-exp
  (lambda (var exp)
    (list 'lambda var exp)))

(define lambda-exp->bound-var
  (lambda (exp)
    (cadr exp)))
