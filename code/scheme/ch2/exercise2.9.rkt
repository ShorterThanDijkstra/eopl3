#lang eopl
(require "exercise2.5.rkt")
(require rackunit)

; Env = (empty-env) | (extend-env Var SchemeVal Env)
; Var = Sym
(define has-binding?
  (lambda (env s)
    (cond
      [(equal? env '()) #f]
      [(equal? s (caar env)) #t]
      [else (has-binding? (cdr env) s)])))

;;; test

(define env
  (extend-env 'd 6
              (extend-env 'y 8
                          (extend-env 'x 7
                                      (extend-env 'y 14
                                                  (empty-env))))))

(check-equal? (has-binding? env 'y) #t)
(check-equal? (has-binding? env 'z) #f)

