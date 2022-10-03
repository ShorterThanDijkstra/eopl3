#lang eopl
(require rackunit)

(define (identifier? x)
  (and (symbol? x) (not (eqv? x 'lambda))))

(define-datatype lc-exp lc-exp?
  [var-exp
   (var identifier?)]
  [lambda-exp
   (bound-var identifier?)
   (body lc-exp?)]
  [app-exp
   (rator lc-exp?)
   (rand lc-exp?)])
