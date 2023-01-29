#lang eopl
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Grammar
(define identifier? (lambda (exp) (and (symbol? exp) (not (eqv? exp 'lambda)))))

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define the-grammar
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("proc" "(" identifier optional-type ")" expression) proc-exp)
    (expression ("(" expression expression ")") call-exp)
    (expression ("letrec" optional-type
                          identifier
                          "("
                          identifier
                          optional-type
                          ")"
                          "="
                          expression
                          "in"
                          expression)
                letrec-exp)
    (optional-type (":" type) a-type)
    (optional-type (type) a-type)
    (optional-type () no-type)
    (type ("int") int-type)
    (type ("bool") bool-type)
    (type ("(" type "->" type ")") proc-type)))
(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse (sllgen:make-string-parser the-lexical-spec the-grammar))

;;; test
(scan&parse
 "proc(x) if x then 1 else 0")

(scan&parse
 "proc(x: bool) if x then 1 else 0")

(scan&parse
 "letrec f (x : int)
    = if zero?(x) then 0 else -((f -(x,1)), -2)
  in f")

(scan&parse
"letrec even (odd)
             = proc (x) if zero?(x)
                        then 1
                        else (odd -(x,1))
   in letrec int odd (x: int) =
                if zero?(x)
                then 0
                else ((even odd) -(x,1))
      in (odd 13)"
)
