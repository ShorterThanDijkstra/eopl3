#lang eopl
(require "TYPE-OO.rkt")
(require rackunit)

(define ans
  "
  class tree extends object
    method int initialize() 0
    method int sum () 0
    method bool equal (t : tree) false
  
  class interior-node extends tree
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
  
  class leaf-node extends tree
    field int value
    method void initialize (v : int) set value = v
    method int sum () value
    method int getvalue () value
    method bool equal (t : tree)
      if instanceof t leaf-node
      then zero?(-(value, send cast t leaf-node getvalue()))
      else zero?(1)

   let o1 = new interior-node (
               new interior-node (
                   new leaf-node(3),
                   new leaf-node(4)),
               new leaf-node(5))
   in list(send o1 sum(),
          if send o1 equal(o1) then 100 else 200)
  ")

(check-equal? (:t ans) (list-type (int-type)))
(check-equal? (:e ans) (list-val (list (num-val 12) (num-val 100))))