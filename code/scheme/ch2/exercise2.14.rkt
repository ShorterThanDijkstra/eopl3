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
          [check-empty (lambda () #t)]
          [check-binding (lambda (var) #f)])
      (list search check-empty check-binding))))

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
          [check-empty (lambda () #f)]
          [check-binding (lambda (var)
                           (if (eqv? var saved-var)
                               #t
                               (has-binding? saved-env var)))])
      (list search check-empty check-binding))))

(define apply-env
  (lambda (env search-var)
    ((car env) search-var)))

(define has-binding?
  (lambda (env var)
    ((caddr env) var)))

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

(check-equal? (has-binding? env 'y) #t)
(check-equal? (has-binding? env 'x) #t)
(check-equal? (has-binding? env 'm) #f)

