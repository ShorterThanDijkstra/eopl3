#lang eopl
(require rackunit)
(require "exercise1.31.rkt")

; Bintree ::= Int | (Symbol Bintree Bintree)

(define (double-tree bin-tree)
  (if (leaf? bin-tree) (* bin-tree 2)
      (interior-node (contents-of bin-tree)
                     (double-tree (lson bin-tree))
                     (double-tree (rson bin-tree)))))

(define left (interior-node 'left 114 514))
(define right (leaf 114514))
(define test-case (interior-node 'root left right))
(check-equal? (double-tree test-case)
              '(root (left 228 1028) 229028))

