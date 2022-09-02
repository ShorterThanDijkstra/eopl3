#lang eopl
(require rackunit)

(define subst-slist
  (lambda (new old slist)
    (if (null? slist)
        '()
        (cons (subst-expr new old (car slist))
              (subst-slist new old (cdr slist))))))

(define subst-expr
  (lambda (new old sexpr)
    (if (symbol? sexpr)
        (if (eqv? old sexpr)
            new
            sexpr)
        (subst-slist new old sexpr))))

(define subst
  (lambda (new old expr)
    (cond [(null? expr)
           '()]
          [(symbol? (car expr))
           (if (eqv? old (car expr))
               (cons new (subst new old (cdr expr)))
               (cons (car expr) (subst new old (cdr expr))))]
          [else (cons (subst new old (car expr))
                      (subst new old (cdr expr)))])))

;;; test
(check-equal? (subst 'a 'b '((b c) (b () d)))
              '((a c) (a () d)))