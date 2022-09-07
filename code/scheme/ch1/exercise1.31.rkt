#lang eopl
(require rackunit)

; Bintree ::= Int | (Symbol Bintree Bintree)
(define (leaf n) n)

(define (interior-node sym left right)
  (list sym left right))

(define (leaf? bin-tree) (integer? bin-tree))

(define (lson bin-tree)
  (if (leaf? bin-tree) '()
      (cadr bin-tree)))

(define (rson bin-tree)
  (if (leaf? bin-tree) '()
      (caddr bin-tree)))

(define (contents-of bin-tree)
  (if (leaf? bin-tree) bin-tree
      (car bin-tree)))


(check-equal? (leaf 114) 114)
(check-equal? (interior-node 'foo 114 514) '(foo 114 514))
(check-equal? (leaf? (leaf 114514)) #t)
(check-equal? (leaf? (interior-node 'foo 114 514)) #f)
(check-equal? (lson (interior-node 'foo 114 514)) 114)
(check-equal? (rson (interior-node 'foo 114 514)) 514)
(check-equal? (contents-of (interior-node 'foo 114 514)) 'foo)

(provide
 leaf
 leaf?
 interior-node
 lson
 rson
 contents-of)

