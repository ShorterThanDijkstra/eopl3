#lang eopl
(require rackunit)

; Prefix-list ::= (Prefix-exp)
; Prefix-exp  ::= Int
;             ::= - Prefix-exp Prefix-exp


(define-datatype prefix-exp prefix-exp?
  (const-exp
   (num integer?))
  (diff-exp
   (operand1 prefix-exp?)
   (operand2 prefix-exp?)))

(define (const-exp-start? exp)
  (integer? (car exp)))

(define (diff-exp-start? exp)
  (eqv? (car exp) '-))

(define (end? exp)
  (null? exp))

(define (parse-prefix-exp-helper exp)
  (cond [(end? exp) (list '() '())]
        [(const-exp-start? exp)
         (list (const-exp (car exp)) (cdr exp))]
        [(diff-exp-start? exp)
         (let* ([parsed1 (parse-prefix-exp-helper (cdr exp))]
                [prefix-exp1 (car parsed1)]
                [rest1 (cadr parsed1)]
                [parsed2 (parse-prefix-exp-helper rest1)]
                [prefix-exp2 (car parsed2)]
                [rest2 (cadr parsed2)])
           (list (diff-exp prefix-exp1 prefix-exp2) rest2))]))

(define (parse-prefix-exp exp)
  (car (parse-prefix-exp-helper exp)))
;;; test
(define datum '(- - 3 2 - 4 - 12 7))
(define expected (diff-exp
                  (diff-exp
                   (const-exp 3)
                   (const-exp 2))
                  (diff-exp
                   (const-exp 4)
                   (diff-exp
                    (const-exp 12)
                    (const-exp 7)))))

(check-equal? (parse-prefix-exp datum) expected)