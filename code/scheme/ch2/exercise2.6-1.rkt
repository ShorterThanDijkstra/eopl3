#lang eopl
(require rackunit)

; Env = (empty-env) | (extend-env Var SchemeVal Env)
; Var = Sym


(define empty-env
  (lambda () '()))

(define extend-env
  (lambda (var val env)
    (cons var (cons val env))))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define apply-env
  (lambda (env search-var)
    (cond
      [(equal? env (empty-env)) (report-no-binding-found search-var)]
      [(eqv? (car env) search-var) (cadr env)]
      [else (apply-env (cddr env) search-var)])))

;;; test

(define env
  (extend-env 'd 6
              (extend-env 'y 8
                          (extend-env 'x 7
                                      (extend-env 'y 14
                                                  (empty-env))))))

(check-equal? (apply-env env 'd) 6)
(check-equal? (apply-env env 'y) 8)
(check-equal? (apply-env env 'x) 7)

(apply-env env 'z)