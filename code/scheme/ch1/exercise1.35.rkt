#lang eopl
(require rackunit)
(require "exercise1.31.rkt")

; Bintree ::= Int | (Symbol Bintree Bintree)
;;; contract: bintree * leaf-index -> (list leaf-index-after-traverse bintree-after-traverse)
(define (traverse bin-tree leaf-index)
  (if (leaf? bin-tree) (list (+ leaf-index 1) leaf-index)
      (let [(left-traverse (traverse (lson bin-tree) leaf-index))]
        (let [(leaf-index-after-left (car left-traverse))
              (left-son (cadr left-traverse))]
          (let [(right-traverse (traverse (rson bin-tree) leaf-index-after-left))]
            (let [(leaf-index-after-right (car right-traverse))
                  (right-son (cadr right-traverse))]
              (list leaf-index-after-right (interior-node (contents-of bin-tree) left-son right-son))))))))

(define (number-leaves bin-tree)
  (cadr (traverse bin-tree 0)))


(define test-case (interior-node 'foo
                                 (interior-node 'bar
                                                (leaf 26)
                                                (leaf 12))
                                 (interior-node 'baz
                                                (leaf 11)
                                                (interior-node 'quux
                                                               (leaf 117)
                                                               (leaf 14)))))
(check-equal? (number-leaves test-case)
              '(foo (bar 0 1)
                    (baz
                     2
                     (quux 3 4))))
