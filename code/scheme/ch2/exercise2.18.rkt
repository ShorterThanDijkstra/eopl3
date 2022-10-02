#lang eopl
(require rackunit)

(define number->sequence
  (lambda (i)
    (list i '() '())))

(define current-element
  (lambda (seq)
    (car seq)))

(define left
  (lambda (seq)
    (cadr seq)))

(define left-first
  (lambda (seq)
    (car (left seq))))

(define left-rest
  (lambda (seq)
    (cdr (left seq))))

(define right
  (lambda (seq)
    (caddr seq)))

(define right-first
  (lambda (seq)
    (car (right seq))))

(define right-rest
  (lambda (seq)
    (cdr (right seq))))

(define move-to-left
  (lambda (seq)
    (if (null? (left seq))
        (eopl:error "error")
        (list (left-first seq)
              (left-rest seq)
              (cons (current-element seq) (right seq))))))

(define move-to-right
  (lambda (seq)
    (if (null? (right seq))
        (eopl:error "error")
        (list (right-first seq)
              (cons (current-element seq) (left seq))
              (right-rest seq)))))

(define insert-to-left
  (lambda (i seq)
    (list (current-element seq)
          (cons i (left seq))
          (right seq))))

(define insert-to-right
  (lambda (i seq)
    (list (current-element seq)
          (left seq)
          (cons i (right seq)))))

;;; test
(check-equal? (number->sequence 7) '(7 ()()))
(check-equal? (current-element '(6 (5 4 3 2 1) (7 8 9))) 6)
(check-equal? (move-to-left '(6 (5 4 3 2 1) (7 8 9))) '(5 (4 3 2 1) (6 7 8 9)))
(check-equal? (move-to-right '(6 (5 4 3 2 1) (7 8 9))) '(7 (6 5 4 3 2 1) (8 9)))
(check-equal? (insert-to-left 13 '(6 (5 4 3 2 1) (7 8 9))) '(6 (13 5 4 3 2 1) (7 8 9)))
(check-equal? (insert-to-right 13 '(6 (5 4 3 2 1) (7 8 9))) '(6 (5 4 3 2 1) (13 7 8 9)))