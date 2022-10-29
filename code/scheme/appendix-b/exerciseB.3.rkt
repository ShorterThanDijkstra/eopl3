#lang eopl
(require rackunit)

(define scanner-spec-1
  '((number (digit (arbno digit)) number)))

(define  grammar-1
  '((Arith-expr (Arith-term (arbno Additive-op Arith-term)) add-and-sub)
    (Arith-term (Arith-factor (arbno Multiplicative-op Arith-factor)) mul-and-div)
    (Arith-factor (number) number-factor)
    (Arith-factor ("("  Arith-expr ")" ) arith-expr-factor)
    (Additive-op ("+")  add-op)
    (Additive-op ("-") minus-op)
    (Multiplicative-op ("*") mul-op)
    (Multiplicative-op  ("/") div-op)))

(sllgen:make-define-datatypes scanner-spec-1 grammar-1)


(define list-the-datatypes
  (lambda ()
    (sllgen:list-define-datatypes scanner-spec-1 grammar-1)))

(define scan&parse
  (sllgen:make-string-parser scanner-spec-1 grammar-1))

(define value-of-arith-expr
  (lambda (expr)
    (cases Arith-expr expr
      [add-and-sub (term additive-ops terms)
                   (let ([init-val (value-of-arith-term term)]
                         [op-vals (map (lambda (op) (value-of-additive-op op)) additive-ops)]
                         [term-vals (map (lambda (term) (value-of-arith-term term)) terms)])
                     (let eval ([res init-val]
                                [ops op-vals]
                                [vals term-vals])
                       (if (null? ops)
                           res
                           (eval ((car ops) res (car vals)) (cdr ops) (cdr vals)))))])))

(define value-of-additive-op
  (lambda (op)
    (cases Additive-op op
      [add-op () +]
      [minus-op () -])))

(define value-of-arith-term
  (lambda (term)
    (cases Arith-term term
      [mul-and-div (factor mul-ops factors)
                   (let ([init-val (value-of-arith-factor factor)]
                         [op-vals (map (lambda (op) (value-of-multiplicative-op op)) mul-ops)]
                         [factor-vals (map (lambda (factor) (value-of-arith-factor factor)) factors)])
                     (let eval ([res init-val]
                                [ops op-vals]
                                [vals factor-vals])
                       (if (null? ops)
                           res
                           (eval ((car ops) res (car vals)) (cdr ops) (cdr vals)))))])))

(define value-of-arith-factor
  (lambda (factor)
    (cases Arith-factor factor
      [number-factor (num) num]
      [arith-expr-factor (arith-expr)
                         (value-of-arith-expr arith-expr)])))

(define value-of-multiplicative-op
  (lambda (op)
    (cases Multiplicative-op op
      [mul-op () *]
      [div-op () /])))

(define value-of
  (lambda (expr)
    (value-of-arith-expr expr)))

(define run
  (lambda (code)
    (value-of (scan&parse code))))

(check-equal? (run "3+2*66-5") (- (+ 3 (* 2 66)) 5))
(check-equal? (run "3+2*66-5*130") (- (+ 3 (* 2 66)) (* 5 130)))
