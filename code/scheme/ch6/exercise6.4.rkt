#lang eopl
(define end-cont (lambda (v) (begin (eopl:printf "End of computation.~%") v)))


(define remove-first
  (lambda (s los)
    (if (null? los)
        '()
        (if (eqv? (car los) s)
            (cdr los)
            (cons (car los) (remove-first s (cdr los)))))))

(define remove-first/k
  (lambda (s los k)
    (if (null? los)
        (k '())
        (if (eqv? (car los) s)
            (k (cdr los))
            (remove-first/k s (cdr los)
                            (lambda (v0)
                              (k (cons (car los) v0))))))))

(remove-first 'a '(b c a d a))
(remove-first/k 'a '(b c a d a) end-cont)


(define list-sum
  (lambda (loi)
    (if (null? loi)
        0
        (+ (car loi)
           (list-sum (cdr loi))))))

(define list-sum/k
  (lambda (loi k)
    (if (null? loi)
        (k 0)
        (list-sum/k (cdr loi)
                    (lambda (v0)
                      (k (+ (car loi)
                            v0)))))))

(list-sum '(1 2 3 4))
(list-sum/k '(1 2 3 4) end-cont)

(define occurs-free?
  (lambda (var expr)
    (cond [(symbol? expr) (eqv? var expr)]
          [(eqv? (car expr) 'lambda)
           (let ((var_ (caadr expr))
                 (expr_ (caddr expr)))
             (and (not (eqv? var_ var))
                  (occurs-free? var expr_)))]
          [else (let ((expr_ (car expr))
                      (expr__ (cadr expr)))
                  (or (occurs-free? var expr_)
                      (occurs-free? var expr__)))])))

(define occurs-free/k?
  (lambda (var expr k)
    (cond [(symbol? expr)
           (k (eqv? var expr))]
          [(eqv? (car expr) 'lambda)
           (let ((var_ (caadr expr))
                 (expr_ (caddr expr)))
             (occurs-free/k? var expr_
                             (lambda (v0)
                               (k (and (not (eqv? var_ var))
                                       v0)))))]
          [else (let ((expr_ (car expr))
                      (expr__ (cadr expr)))
                  (occurs-free/k? var expr_
                                  (lambda (v0)
                                    (occurs-free/k? var expr__
                                                    (lambda (v1)
                                                      (k (or v0 v1)))))))])))

(occurs-free? 'x '(lambda (y) (lambda (z) (x (y z)))))
(occurs-free/k? 'x '(lambda (y) (lambda (z) (x (y z)))) end-cont)

(define subst
  (lambda (new old slist)
    (if (null? slist)
        '()
        (cons
         (subst-in-s-exp new old (car slist))
         (subst new old (cdr slist))))))
(define subst-in-s-exp
  (lambda (new old sexp)
    (if (symbol? sexp)
        (if (eqv? sexp old) new sexp)
        (subst new old sexp))))

(define subst/k
  (lambda (new old slist k)
    (if (null? slist)
        (k '())
        (subst-in-s-exp/k new old (car slist)
                          (lambda (v0)
                            (subst/k new old (cdr slist)
                                     (lambda (v1)
                                       (k (cons v0 v1)))))))))
(define subst-in-s-exp/k
  (lambda (new old sexp k)
    (if (symbol? sexp)
        (if (eqv? sexp old) (k new) (k sexp))
        (subst/k new old sexp k))))

(subst 'a 'b '(a b c d e))
(subst/k 'a 'b '(a b c d e) end-cont)
