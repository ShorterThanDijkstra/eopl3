#lang eopl
(require rackunit)
(require "exercise2.5.rkt")

; Env = (empty-env) | (extend-env Var SchemeVal Env)
; Var = Sym


(define empty-env?
  (lambda (env)
    (equal? env '())))

;;; test

(define env
  (extend-env 'd 6
              (extend-env 'y 8
                          (extend-env 'x 7
                                      (extend-env 'y 14
                                                  (empty-env))))))

(check-equal? (empty-env? (empty-env)) #t)
(check-equal? (empty-env? env) #f)


