#lang eopl
(require rackunit)

; Diff-tree ::= (one) | (diff Diff-tree Diff-tree)

(define zero (lambda () '(diff (one) (one))))

(define diff-tree-left
  (lambda (d-tree)
    (cadr d-tree)))

(define diff-tree-right
  (lambda (d-tree)
    (caddr d-tree)))

(define make-diff-tree
  (lambda (left right)
    (list 'diff-tree left right)))

(define diff-tree->number
  (lambda (d-tree)
    (if (equal? d-tree '(one))
        1
        (- (diff-tree->number (diff-tree-left d-tree))
           (diff-tree->number (diff-tree-right d-tree))))))

(define is-zero?
  (lambda (d-tree)
    (= (diff-tree->number d-tree) 0)))

; (define successor
;   (lambda (d-tree)
;     (let [(two (make-diff-tree '(one) (make-diff-tree (zero) '(one))))]
;       (if (equal? d-tree '(one))
;           two
;           (make-diff-tree (successor (diff-tree-left d-tree))
;                           (diff-tree-right d-tree))))))

(define successor
  (lambda (d-tree)
   (let [(minus-one (make-diff-tree (make-diff-tree '(one) '(one)) '(one)))]
     (make-diff-tree d-tree minus-one))))

; (define predecessor
;   (lambda (d-tree)
;     (if (equal? d-tree '(one))
;         (zero)
;         (make-diff-tree (predecessor (diff-tree-left d-tree))
;                         (diff-tree-right d-tree)))))

(define predecessor
  (lambda (d-tree)
    (make-diff-tree d-tree '(one))))

; m + n = m - (-n)
(define diff-tree-plus
  (lambda (m n)
    (define negate
      (lambda (d-tree)
        (make-diff-tree (zero) d-tree)))
    (make-diff-tree m (negate n))))


;;; test
(define MAX 999)
(define MIN -999)

(define number->diff-tree
  (lambda (num)
    (cond [(= num 0) (zero)]
          [(< num 0) (predecessor (number->diff-tree (+ num 1)))]
          [else (successor (number->diff-tree (- num 1)))])))


(define (check-successor d-tree index)
  (cond [(= index MAX) #t]
        [(= (diff-tree->number d-tree) index)
         (check-successor (successor d-tree) (+ index 1))]
        [else #f]))
(check-equal? (check-successor (number->diff-tree MIN) MIN) #t)


(define (check-predecessor d-tree index)
  (cond [(= index MIN) #t]
        [(= (diff-tree->number d-tree) index)
         (check-predecessor (predecessor d-tree) (- index 1))]
        [else #f]))
(check-equal? (check-predecessor (number->diff-tree MAX) MAX) #t)

(define MAX-DIFF-PLUS 200)
(define MIN-DIFF-PLUS -200)

(define MAX-DIFF-TREE (number->diff-tree MAX-DIFF-PLUS))
(define (check-diff-tree-plus m-d-tree n-d-tree m-num n-num)
  (begin
    (write (list m-num n-num))
    (newline)
    (cond
      [(not (= (diff-tree->number (diff-tree-plus m-d-tree n-d-tree)) (+ m-num n-num))) #f]
      [(and (= m-num MIN-DIFF-PLUS) (= n-num MIN-DIFF-PLUS)) #t]
      [(= m-num MIN-DIFF-PLUS) (check-diff-tree-plus MAX-DIFF-TREE (predecessor n-d-tree) MAX-DIFF-PLUS (- n-num 1))]
      [else (check-diff-tree-plus (predecessor m-d-tree) n-d-tree (- m-num 1) n-num)])))
(check-equal? (check-diff-tree-plus MAX-DIFF-TREE MAX-DIFF-TREE MAX-DIFF-PLUS MAX-DIFF-PLUS) #t)


(define two  (make-diff-tree '(one) (make-diff-tree (zero) '(one))))
(define three (successor two))
