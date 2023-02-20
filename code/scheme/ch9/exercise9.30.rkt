#lang eopl
(require "TYPE-OO.rkt")
(require rackunit)

(define summable-lists
  "
  interface summable
    method int sum ()

  class summable-list extends object implements summable
    field listof int ls
    method void initialize(l: listof int) set ls = l
    method int sum-rec(l: listof int)
      if null?(l)
      then 0
      else +(car(l), send self sum-rec(cdr(l)))
    method int sum()
      send self sum-rec(ls)

  let sl = new summable-list(list(13, 31, 37, 73))
  in send sl sum()")

(check-equal? (:t summable-lists) (int-type))
(check-equal? (:e summable-lists) (num-val 154))

#|
  interface tree
    method int sum ()
    method bool equal (t : tree)
  
  class interior-node extends object implements tree
    field tree left
    field tree right
    method void initialize(l : tree, r : tree)
      begin
      set left = l; set right = r
      end
    method tree getleft () left
    method tree getright () right
    method int sum () +(send left sum(), send right sum())
    method bool equal (t : tree)
      if instanceof t interior-node
      then if send left equal(send cast t interior-node getleft())
           then send right equal(send cast t interior-node getright())
           else zero?(1)
      else zero?(1)
  class leaf-node extends object implements tree
    field int value
    method void initialize (v : int) set value = v
    method int sum () value
    method int getvalue () value
    method bool equal (t : tree)
      if instanceof t leaf-node
      then zero?(-(value, send cast t leaf-node getvalue()))
      else zero?(1)
|#
(define  summable-binary-trees
  "
  interface summable
    method int sum ()

  class interior-node extends object implements summable
    field summable left
    field summable right
  method void initialize(l : summable, r : summable)
    begin
    set left = l; set right = r
    end
  method int sum () +(send left sum(), send right sum())
  
  
  class leaf-node extends object implements summable
    field int value
    method void initialize (v : int) set value = v
    method int sum () value
  
  let o1 = new interior-node (
               new interior-node (
                   new leaf-node(3),
                   new leaf-node(4)),
               new leaf-node(5))
  in send o1 sum()")
  
(check-equal? (:t summable-binary-trees)  (int-type))
(check-equal? (:e summable-binary-trees) (num-val 12))

(define summable-general-trees
  "
  interface summable
    method int sum ()

  class summable-list extends object implements summable
    field listof int ls
    method void initialize(l: listof int) set ls = l
    method int sum-rec(l: listof int)
      if null?(l)
      then 0
      else +(car(l), send self sum-rec(cdr(l)))
    method int sum()
      send self sum-rec(ls)

  class summable-general-tree extends object implements summable
    field summable-list left
    field summable-list right
    method void initialize(l:  summable-list, r:  summable-list)
      begin set left = l; set right = r end
    method int sum() +(send left sum(), send right sum())

  let sl = new summable-list(list(13, 31, 37, 73))
  in let st = new summable-general-tree(sl, sl)
  in send st sum()
  ")
  
(check-equal? (:t summable-general-trees)  (int-type))
(check-equal? (:e summable-general-trees) (num-val 308))

; stringable, skip