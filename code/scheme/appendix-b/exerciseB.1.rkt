#lang eopl

(define scanner-spec-1
  '((number (digit (arbno digit)) number)))

(define  grammar-1
  '((Arith-expr (Arith-term (arbno Additive-op Arith-term)) add-or-sub)
    (Arith-term (Arith-factor (arbno Multiplicative-op Arith-factor)) mul-or-div)
    (Arith-factor (number) number-factor)
    (Arith-factor ("("  Arith-expr ")" ) arith-factor)
    (Additive-op ("+")  add-op)
    (Additive-op ("-") minus-op)
    (Multiplicative-op ("*") mul-op)
    (Multiplicative-op  ("/") div-op)))

(sllgen:make-define-datatypes scanner-spec-1 grammar-1)

(define scan&parse
  (sllgen:make-string-parser scanner-spec-1 grammar-1))


(define parsed (scan&parse "3+2*66-5"))