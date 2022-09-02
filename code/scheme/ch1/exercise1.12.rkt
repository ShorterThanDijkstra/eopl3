#lang eopl
(require rackunit)

(define subst
  (lambda (new old slist)
    (if (null? slist)
        '()
        (cons
         ;  (subst-in-s-exp new old (car slist))
         (if (symbol? (car slist))
             (if (eqv? (car slist) old) new (car slist))
             (subst new old (car slist)))
         (subst new old (cdr slist))))))

; (define subst-in-s-exp
;   (lambda (new old sexp)
;     (if (symbol? sexp)
;         (if (eqv? sexp old) new sexp)
;         (subst new old sexp))))

(check-equal? (subst 'a 'b '((b c) (b () d)))
              '((a c) (a () d)))