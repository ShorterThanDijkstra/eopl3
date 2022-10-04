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

(define (parse-expression  datum)
  (cond [(identifier? datum) (Var-exp datum)]
        [(pair? datum)
         (if (eqv? (car datum) 'lambda)
             (Lambda-exp (cadr datum)  (parse-expression  (caddr datum)))
             (App-exp (parse-expression  (car datum))
                      (map parse-expression (cdr datum))))]
        [else (eopl:error "error")]))


;;; test
(define datum '(lambda (x) (lambda (y z) ((lambda (x)(x y)) x y z))))
(define expect (Lambda-exp
                '(x)
                (Lambda-exp
                 '(y z)
                 (App-exp
                  (Lambda-exp '(x) (App-exp (Var-exp 'x) (list (Var-exp 'y))))
                  (list (Var-exp 'x) (Var-exp 'y) (Var-exp 'z))))))
(check-equal? (parse-expression  datum) expect)