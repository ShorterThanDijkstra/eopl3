#lang eopl
(require "exercise2.5.rkt")
(require rackunit)

(define extend-env*
  (lambda (vars vals env)
    (if (null? vars)
        env
        (extend-env (car vars) (car vals) (extend-env* (cdr vars) (cdr vals) env)))))


;;; test
(define env
  (extend-env* '(d y x y) '(6 8 7 14) (empty-env)))

(check-equal? (apply-env env 'd) 6)
(check-equal? (apply-env env 'y) 8)
(check-equal? (apply-env env 'x) 7)