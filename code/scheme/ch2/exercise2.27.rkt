#lang eopl
(require rackunit)

(define-datatype Red-blue-tree red-blue-tree?
  [A-red-blue-subtree])

(define-datatype Red-blue-subtree red-blue-subtree?
  [Red-node
   (lson red-blue-subtree?)
   (rson red-blue-subtree?)]
  [Blue-node (red-blue-subtrees (list-of red-blue-subtree?))]
  [Leaf-node (val integer?)])

(define (count-red rbstree count)
  (cases Red-blue-subtree rbstree
    [Red-node (lson rson) (Red-node (count-red lson (+ count 1)) (count-red rson (+ count 1)))]
    [Blue-node (children) (Blue-node (map (lambda (child) (count-red child count)) children))]
    [Leaf-node (_) (Leaf-node count)]))

(define (mark-leaves-with-red-depth red-blue-tree)
  (count-red red-blue-tree 0))


;;; test
(define test-case
  (Red-node
   (Blue-node
    (list
     (Leaf-node 26)
     (Leaf-node 12)))
   (Red-node
    (Leaf-node 11)
    (Blue-node
     (list
      (Leaf-node 117)
      (Leaf-node 14))))))

(define answer
  (Red-node
   (Blue-node
    (list
     (Leaf-node 1)
     (Leaf-node 1)))
   (Red-node
    (Leaf-node 2)
    (Blue-node
     (list
      (Leaf-node 2)
      (Leaf-node 2))))))

(check-equal? (mark-leaves-with-red-depth test-case) answer)