#lang eopl
(require rackunit)

; Lc-exp ::= Identifier
;        ::= (lambda (Identifier) Lc-exp)
;        ::= (Lc-exp Lc-exp)

(define var-exp
  (lambda (var)
    var))

(define lambda-exp
  (lambda (var exp)
    (list 'lambda (list var) exp)))

(define app-exp
  (lambda (exp1 exp2)
    (list exp1 exp2)))

(define var-exp?
  (lambda (exp)
    (symbol? exp)))

(define lambda-exp?
  (lambda (exp)
    (and (list? exp)
         (eqv? (car exp) 'lambda))))

(define exp?
  (lambda (exp)
    (or (var-exp? exp)
        (lambda-exp? exp)
        (app-exp? exp))))

(define app-exp?
  (lambda (exp)
    (and (exp? (app-exp->rator exp))
         (exp? (app-exp->rand exp)))))

(define var-exp->var
  (lambda (exp)
    exp))

(define lambda-exp->bound-var
  (lambda (exp)
    (caadr exp)))

(define lambda-exp->body
  (lambda (exp)
    (caddr exp)))

(define app-exp->rator
  (lambda (exp)
    (car exp)))

(define app-exp->rand
  (lambda (exp)
    (cadr exp)))

(define occurs-free?
  (lambda (search-var exp)
    (cond
      ((var-exp? exp) (eqv? search-var (var-exp->var exp)))
      ((lambda-exp? exp)
       (and
        (not (eqv? search-var (lambda-exp->bound-var exp)))
        (occurs-free? search-var (lambda-exp->body exp))))
      (else
       (or
        (occurs-free? search-var (app-exp->rator exp))
        (occurs-free? search-var (app-exp->rand exp)))))))

;;; test
(let [(exprs '('x
               'y
               '(lambda (x) (x y))
               '(lambda (y) (x y))
               '((lambda (x) x) (x y))
               '(lambda (y) (lambda (z) (x (y z))))))
      (answers '(#t #f #f #t #t #t))
      (test (lambda (expr answer) (check-equal? (occurs-free? 'x expr) answer)))]
  (map test exprs answers))