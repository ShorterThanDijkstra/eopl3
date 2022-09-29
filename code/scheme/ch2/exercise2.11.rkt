#lang eopl
(require rackunit)

(define empty-env
  (lambda () '()))

(define extend-env
  (lambda (var val env)
    (cons (list (list var) (list val)) env)))

(define extend-env*
  (lambda (vars vals env)
    (cons (list vars vals) env)))


(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define nothing
  (list 'nothing))

(define just
  (lambda (val) (list 'just val)))

(define search-rib
  (lambda (search-var vars vals)
    (cond [(null? vars) nothing]
          [(eqv? (car vars) search-var) (just (car vals))]
          [else (search-rib search-var (cdr vars) (cdr vals))])))

(define apply-env
  (lambda (env search-var)
    (if (equal? env '())
        (report-no-binding-found search-var)
        (let ([search-res (search-rib search-var (caar env) (cadar env))])
          (if (equal? search-res '(nothing))
              (apply-env (cdr env) search-var)
              (cadr search-res))))))


;;; test
(define env
  (extend-env* '(a b c) '(11 12 13)
   (extend-env* '(x y) '(66 77)
    (extend-env* '(x y) '(88 99)
     (extend-env 'm 3 (empty-env))))))


(check-equal? (apply-env env 'a) 11)
(check-equal? (apply-env env 'b) 12)
(check-equal? (apply-env env 'c) 13)
(check-equal? (apply-env env 'x) 66)
(check-equal? (apply-env env 'y) 77)
(check-equal? (apply-env env 'm) 3)

