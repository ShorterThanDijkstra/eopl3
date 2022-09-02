#lang eopl
(require rackunit)

(define occurs-free?
  (lambda (var expr)
    (cond [(symbol? expr) (eqv? var expr)]
          [(eqv? (car expr) 'lambda)
           (let [(var_ (caadr expr))
                 (expr_ (caddr expr))]
             (and (not (eqv? var_ var))
                  (occurs-free? var expr_)))]
          [else (let [(expr_ (car expr))
                      (expr__ (cadr expr))]
                  (or (occurs-free? var expr_)
                      (occurs-free? var expr__)))])))

;;; test
;;; (check-equal? (occurs-free? 'x 'x) #t)
;;; (check-equal? (occurs-free? 'x 'y) #f)
;;; (check-equal? (occurs-free? 'x '(lambda (x) (x y))) #f)
;;; (check-equal? (occurs-free? 'x '(lambda (y) (x y))) #t)
;;; (check-equal? (occurs-free? 'x '((lambda (x) x) (x y))) #t)
;;; (check-equal? (occurs-free? 'x '(lambda (y) (lambda (z) (x (y z))))) #t)

(let [(exprs '('x
               'y
               '(lambda (x) (x y))
               '(lambda (y) (x y))
               '((lambda (x) x) (x y))
               '(lambda (y) (lambda (z) (x (y z))))))
      (answers '(#t #f #f #t #t #t))
      (test (lambda (expr answer) (check-equal? (occurs-free? 'x expr) answer)))]
  (map test exprs answers))



