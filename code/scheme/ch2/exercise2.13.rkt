#lang eopl
(require rackunit)


(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))
(define empty-env
  (lambda ()
    (let ([search
           (lambda (search-var)
             (report-no-binding-found search-var))]
          [check (lambda () #t)])
      (list search check))))

(define empty-env?
  (lambda (env)
    ((cadr env))))

(define extend-env
  (lambda (saved-var saved-val saved-env)
    (let ([search
           (lambda (search-var)
             (if (eqv? search-var saved-var)
                 saved-val
                 (apply-env saved-env search-var)))]
          [check (lambda () #f)])
      (list search check))))

(define apply-env
  (lambda (env search-var)
    ((car env) search-var)))


(provide empty-env empty-env? extend-env apply-env)


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

(check-equal? (empty-env? (empty-env)) #t)
(check-equal? (empty-env? env) #f)