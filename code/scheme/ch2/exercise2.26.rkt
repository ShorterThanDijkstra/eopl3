#lang eopl
(require rackunit)


(define-datatype Bintree bintree?
  [Leaf-node
   (num integer?)]
  [Interior-node
   (key symbol?)
   (left bintree?)
   (right bintree?)])

(define (max-interior-help bintree)
  (cases Bintree bintree
    [Leaf-node (num) (list '() num)]
    [Interior-node
     (key left right)
     (let ([max-and-sum-left (max-interior-help left)]
           [max-and-sum-right (max-interior-help right)])
       (let ([max-left (car max-and-sum-left)]
             [max-right (car max-and-sum-right)]
             [sum-left (cadr max-and-sum-left)]
             [sum-right (cadr max-and-sum-right)])
         (let ([sum (+ sum-left sum-right)])
           (cond [(and (null? max-left) (null? max-right))
                  (list key sum)]
                 [(null? max-left)
                  (if (< sum sum-right)
                      (list max-right sum)
                      (list key sum))]
                 [(null? max-right)
                  (if (< sum sum-left)
                      (list max-left sum)
                      (list key sum))]
                 [(and (> sum sum-left)
                       (> sum sum-right))
                  (list key sum)]
                 [(and (> sum-left sum)
                       (> sum-left sum-right))
                  (list max-right sum)]
                 [(and (> sum-right sum)
                       (> sum-right sum-left))
                  (list max-right sum)]
                 [else (eopl:error "error")]))))]))

(define (max-interior bintree)
  (car (max-interior-help bintree)))


;;; test

(define tree-1
  (Interior-node 'foo (Leaf-node 2) (Leaf-node 3)))
(define tree-2
  (Interior-node 'bar (Leaf-node -1) tree-1))
(define tree-3
  (Interior-node 'baz tree-2 (Leaf-node 1)))


(check-equal? (max-interior tree-1) 'foo)
(check-equal? (max-interior tree-2) 'foo)
(check-equal? (max-interior tree-3) 'baz)

(define tree-4
  (Interior-node 'foo (Leaf-node 2) (Leaf-node -4)))
(define tree-5
  (Interior-node 'bar (Leaf-node -1) tree-1))
(define tree-6
  (Interior-node 'baz tree-2 (Leaf-node 1)))

 (check-equal? (max-interior tree-5) 'foo)
 (check-equal? (max-interior tree-6) 'baz)