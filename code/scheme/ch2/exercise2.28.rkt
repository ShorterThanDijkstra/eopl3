#lang eopl
(require rackunit)

(define (identifier? exp)
  (and (symbol? exp) (not (eqv? 'lambda exp))))

(define (unparse-lc-exp exp)
  (cond [(identifier? exp) (symbol->string exp)]
        [(and (pair? exp)
              (eqv? (car exp) 'lambda)
              (identifier? (caadr exp)))
         (string-append "(lambda ("
                        (unparse-lc-exp (caadr exp))
                        ") "
                        (unparse-lc-exp (caddr exp))
                        ")")]
        [(pair? exp)
         (string-append "("
                        (unparse-lc-exp (car exp))
                        " "
                        (unparse-lc-exp (cadr exp))
                        ")")]
        [else (eopl:error "error")]))


;;; test
(define datum  '(lambda (x) (lambda (y) ((lambda (x) (x y)) x))))
(define expect "(lambda (x) (lambda (y) ((lambda (x) (x y)) x)))")
(check-equal? (unparse-lc-exp datum) expect)