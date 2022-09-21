#lang eopl
(require rackunit)

; Env = (empty-env) | (extend-env Var SchemeVal Env)
; Var = Sym

(define empty-env
  (lambda () '()))

(define extend-env
  (lambda (var val env)
    (cons (cons var val) env)))

(define apply-env
  (lambda (env search-var)
    (cond
      [(eqv? env (empty-env)) (report-no-binding-found search-var)]
      [(eqv? (caar env) search-var) (cdar env)]
      [else (apply-env (cdr env) search-var)])))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))


;;; test

(define env
  (extend-env 'd 6
              (extend-env 'y 8
                          (extend-env 'x 7
                                      (extend-env 'y 14
                                                  (empty-env))))))

(check-equal? (apply-env env 'y) 8)
(apply-env env 'z)

