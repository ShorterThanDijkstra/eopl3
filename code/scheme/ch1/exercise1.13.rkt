#lang eopl
(require rackunit)

(define subst-in-s-exp
  (lambda (new old sexp)
    (if (symbol? sexp)
        (if (eqv? sexp old) new sexp)
        (subst new old sexp))))

(define subst
  (lambda (new old slist)
    (map (lambda (expr) (subst-in-s-exp new old expr)) slist)))

(check-equal? (subst 'a 'b '((b c) (b () d)))
              '((a c) (a () d)))