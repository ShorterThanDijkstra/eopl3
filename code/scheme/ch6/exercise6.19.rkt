#lang eopl
(require rackunit)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; CPS-IN
(define cps-in-lexical-spec
  '([whitespace (whitespace) skip]
    [comment ("%" (arbno (not #\newline))) skip]
    [identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol]
    [number (digit (arbno digit)) number]
    [number ("-" digit (arbno digit)) number]))

(define cps-in-grammar
  '([program (expression) a-program]
    [expression (number) const-exp]
    [expression ("-" "(" expression "," expression ")") diff-exp]
    [expression ("zero?" "(" expression ")") zero?-exp]
    [expression ("if" expression "then" expression "else" expression) if-exp]
    [expression
     ("letrec"
      (arbno identifier "(" (separated-list identifier ",") ")" "=" expression)
      "in"
      expression)
     letrec-exp]
    [expression (identifier) var-exp]
    [expression ("let" identifier "=" expression "in" expression) let-exp]
    [expression
     ("proc" "(" (separated-list identifier ",") ")" expression)
     proc-exp]
    [expression ("(" expression (arbno expression) ")") call-exp]))

(sllgen:make-define-datatypes cps-in-lexical-spec cps-in-grammar)

(define scan&parse
  (sllgen:make-string-parser cps-in-lexical-spec cps-in-grammar))

(define tail-form?
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (tail-form-of? exp1)))))

(define operand-exp?
  (lambda (exp)
    (cases expression
      exp
      (const-exp (num) #t)
      (var-exp (var) #t)
      (diff-exp (exp1 exp2) (and (operand-exp? exp1) (operand-exp? exp2)))
      (zero?-exp (exp1) (operand-exp? exp1))
      (proc-exp (vars body) (tail-form-of? body))
      (else #f))))

(define tail-form-of?
  (lambda (exp)
    (cases expression
      exp
      (const-exp (num) #t)
      (var-exp (var) #t)
      (diff-exp (exp1 exp2) (and (operand-exp? exp1) (operand-exp? exp2)))
      (zero?-exp (exp1) (operand-exp? exp1))
      (if-exp (exp1 exp2 exp3) (and (operand-exp? exp1) (tail-form-of? exp2) (tail-form-of? exp3)))
      (letrec-exp (vars argss exps body) (and (all tail-form-of? exps) (tail-form-of? body)))
      (let-exp (var exp1 body) (and (operand-exp? exp1) (tail-form-of? body)))
      (proc-exp (vars body) (tail-form-of? body))
      (call-exp (rantor rands) (and (operand-exp? rantor) (all operand-exp? rands))))))

(define all
  (lambda (pred lst)
    (if (null? lst)
        #t
        (and (pred (car lst))
             (all pred (cdr lst))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; test
;;; copy from https://github.com/EFanZh/EOPL-Exercises/blob/master/tests/exercise-6.19-test.rkt
(define check
  (lambda (str)
    (tail-form? (scan&parse str))))

(check-true (check "3"))
(check-true (check "-(3, 4)"))
(check-true (check "-(-(3, 4), 4)"))
(check-true (check "-(3, -(3, 4))"))
(check-true (check "zero?(3)"))
(check-true (check "if x then y else z"))
(check-true (check "if x then (y z) else w"))
(check-true (check "x"))
(check-true (check "let x = y in z"))
(check-true (check "let x = y in (z w)"))
(check-true (check "letrec x (y) = z in w"))
(check-true (check "letrec x (y) = (y z) in w"))
(check-true (check "proc (x) y"))
(check-true (check "(x y z)"))

(check-false (check "-((x y), z)"))
(check-false (check "zero?((x y))"))
(check-false (check "if (x y) then z else w"))
(check-false (check "if x then ((y z) w) else u"))
(check-false (check "let x = (y z) in w"))
(check-false (check "letrec x (y) = ((y z) w) in u"))
(check-false (check "proc (x) ((y z) w)"))
(check-false (check "((y z) w)"))