#lang eopl
(require rackunit)

(define-datatype Env env?
  (Empty-env)
  (Extend-env
   (var symbol?)
   (val always?)
   (saved-env env?)))

(define (report-no-binding-found  search-var)
  (eopl:error 'apply-env "No binding for ~s" search-var))

(define (apply-env env search-var)
  (cases Env env
    [Empty-env
     ()
     (report-no-binding-found  search-var)]
    [Extend-env
     (var val saved-env)
     (if (eqv? var search-var)
         val
         (apply-env saved-env search-var))]))

(define (empty-env? env)
  (cases Env env
    [Empty-env () #t]
    [Extend-env (var val saved-env) #f]))

(define (has-binding? env s)
  (cases Env env
    [Empty-env () #f]
    [Extend-env (var val saved-env)
                (if (eqv? var s) #t
                    (has-binding? saved-env s))]))


;;; test
(define env
  (Extend-env 'd 6
              (Extend-env 'y 8
                          (Extend-env 'x 7
                                      (Extend-env 'y 14
                                                  (Empty-env))))))

(check-equal? (apply-env env 'y) 8)
(check-equal? (has-binding? env 'y) #t)
(check-equal? (has-binding? env 'z) #f)