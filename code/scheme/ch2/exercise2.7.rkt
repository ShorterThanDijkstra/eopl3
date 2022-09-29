#lang eopl
(require rackunit)

(define empty-env
  (lambda () (list 'empty-env)))

(define extend-env
  (lambda (var val env)
    (list 'extend-env var val env)))
(define apply-env
  (lambda (origin-env search-var)
    (let ([report-no-binding-found (lambda () (eopl:error 'apply-env "No binding for ~s in ~s" search-var origin-env ))]
          [report-invalid-env (lambda () (eopl:error 'apply-env "Bad environment: ~s" origin-env))])
      (let search ([env origin-env])
        (cond
          ((eqv? (car env) 'empty-env)
           (report-no-binding-found))
          ((eqv? (car env) 'extend-env)
           (let ([saved-var (cadr env)]
                 [saved-val (caddr env)]
                 [saved-env (cadddr env)])
             (if (eqv? search-var saved-var)
                 saved-val
                 (search saved-env))))
          (else
           (report-invalid-env)))))))


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