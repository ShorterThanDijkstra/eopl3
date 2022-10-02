#lang eopl
(require rackunit)

(define number->bintree
  (lambda (num)
    (list num '() '())))

(define current-element
  (lambda (tree)
    (if (null? tree)
        (eopl:error "error")
        (car tree))))

(define move-to-left-son
  (lambda (tree)
    (if (null? tree)
        (eopl:error "error")
        (cadr tree))))

(define move-to-right-son
  (lambda (tree)
    (if (null? tree)
        (eopl:error "error")
        (caddr tree))))

(define at-leaf?
  (lambda (tree)
    (null? tree)))


(define insert-to-left
  (lambda (num tree)
    (list (current-element tree)
          (list num (move-to-left-son tree) '())
          (move-to-right-son tree))))

(define insert-to-right
  (lambda (num tree)
    (list (current-element tree)
          (move-to-left-son tree)
          (list num '() (move-to-right-son tree)))))

;;; test
(define t1 (insert-to-right 14
                            (insert-to-left 12
                                            (number->bintree 13))))
(check-equal? (number->bintree 13) '(13 () ()))
(check-equal? t1 '(13 (12 () ()) (14 () ())))
(check-equal? (move-to-left-son t1) '(12 () ()))
(check-equal? (current-element (move-to-left-son t1)) 12)
(check-equal? (at-leaf? (move-to-right-son (move-to-left-son t1))) #t)
(check-equal? (insert-to-left 15 t1) '(13 (15  (12 () ()) ()) (14 () ())))
