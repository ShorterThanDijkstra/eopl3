#lang eopl

; (define-datatype program program?
;   (a-program
;    (exp1 expression?)))

; (define identifier?
;   (lambda (exp)
;     (and (symbol? exp)
;          (not (eqv? exp 'lambda)))))

; (define-datatype expression expression?
;   (const-exp
;    (num number?))
;   (diff-exp
;    (exp1 expression?)
;    (exp2 expression?))
;   (zero?-exp
;    (exp1 expression?))
;   (if-exp
;    (exp1 expression?)
;    (exp2 expression?)
;    (exp3 expression?))
;   (var-exp
;    (var identifier?))
;   (let-exp
;    (var identifier?)
;    (exp1 expression?)
;    (body expression?)))

;; Define scanner/grammar and create sllgen parser
(define scanner-spec-1
  '((white-sp (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit))) symbol)
    ; (keyword ("lambda") string)
    (number (digit (arbno digit)) number)))

(define grammar-1
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression (identifier) var-exp)
    (expression ("-(" expression "," expression ")") diff-exp)
    (expression ("zero?(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)))

(sllgen:make-define-datatypes scanner-spec-1 grammar-1)

(define list-the-datatypes
  (lambda ()
    (sllgen:list-define-datatypes scanner-spec-1 grammar-1)))

(define scan (sllgen:make-string-scanner scanner-spec-1 grammar-1))

(define scan&parse
  (sllgen:make-string-parser scanner-spec-1 grammar-1))
