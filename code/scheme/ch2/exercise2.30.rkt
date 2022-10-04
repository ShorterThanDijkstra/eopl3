#lang eopl
(require rackunit)


(define (identifier? exp)
  (and (symbol? exp) (not (eqv? 'lambda exp))))

(define-datatype Lc-exp lc-exp?
  [Var-exp
   (var identifier?)]
  [Lambda-exp
   (bound-vars (list-of identifier?))
   (body lc-exp?)]
  [App-exp
   (rator lc-exp?)
   (rands (list-of lc-exp?))])

(define (lc-datum? datum)
  (cond [(identifier? datum) #t]
        [(lambda-datum? datum) #t]
        [(app-datum? datum) #t]
        [else #f]))

(define (lambda-datum? datum)
  (and (and (list? datum)
            (=  (length datum) 3))
       (eqv? 'lambda (car datum))
       (list? (cadr datum))
       (lc-datum? (caddr datum))))

(define (app-datum? datum)
  (and (and (list? datum)
            (> (length datum) 0))
       (lambda-datum? (car datum))))

(define (parse-expression-help datum origin)
  (cond [(identifier? datum) (Var-exp datum)]
        [(lambda-datum? datum)
         (Lambda-exp (cadr datum)  (parse-expression-help (caddr datum) origin))]
        [(app-datum? datum)
         (App-exp (parse-expression-help (car datum) origin)
                  (map parse-expression-help (cdr datum) origin))]
        [else (eopl:error 'parse-expression "Invalid Lc-exp ~s in ~s" datum origin)]))

(define (parse-expression datum)
  (parse-expression-help datum datum))


;;; test
(parse-expression '(lambda (x) ()))

(parse-expression '(lambda))
(parse-expression '(lambda (x)))
(parse-expression '(lambda (x) x y z))
(parse-expression '(a b c))