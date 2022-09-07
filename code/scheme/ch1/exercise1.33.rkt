#lang eopl
(require rackunit)
(require "exercise1.31.rkt")

; Bintree ::= Int | (Symbol Bintree Bintree)

(define (mark-leaves-with-red-depth bin-tree)
  (define (traverse bin-tree count)
    (cond [(leaf? bin-tree) count]
          [(eqv? (contents-of bin-tree) 'red)

           (interior-node (contents-of bin-tree)
                          (traverse (lson bin-tree) (+ count 1))
                          (traverse (rson bin-tree) (+ count 1)))]
          [else  (interior-node (contents-of bin-tree)
                                (traverse (lson bin-tree) count)
                                (traverse (rson bin-tree) count))]))
  (traverse bin-tree 0))

;;; test
(define test-case
  (interior-node 'red
                 (interior-node 'bar
                                (leaf 26)
                                (leaf 12))
                 (interior-node 'red
                                (leaf 11)
                                (interior-node 'quux
                                               (leaf 117)
                                               (leaf 14)))))
(define answer
  '(red
    (bar 1 1)
    (red 2 (quux 2 2))))

(check-equal? (mark-leaves-with-red-depth test-case) answer)