#lang eopl
(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter
      (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define the-grammar-spec
  '((program (statement) a-program)
    (expression (number) const-exp)
    (expression (identifier) var-exp)
    (expression
     ("-" "(" expression "," expression ")")
     diff-exp)
    (expression
     ("*" "(" expression "," expression ")")
     mul-exp)
    (expression ("zero?" "(" expression ")")
                zero?-exp)
    (expression
     ("proc" "(" identifier ")" expression)
     proc-exp)
    (expression ("(" expression expression ")")
                call-exp)
    (statement (identifier "=" expression) assign-stmt)
    (statement ("print" expression) print-stmt)
    (statement ("{" (separated-list  statement ";") "}")
               seq-stmt)
    (statement ("if" expression statement statement)
               if-stmt)
    (statement ("while" expression statement)
               while-stmt)
    (statement ("var" (separated-list identifier ",") ";" statement)
               block-stmt)
    ))
(define list-the-datatypes
  (lambda ()
    (sllgen:list-define-datatypes the-lexical-spec the-grammar-spec)))