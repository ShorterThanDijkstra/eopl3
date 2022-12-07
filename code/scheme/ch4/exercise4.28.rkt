#lang eopl
#|
(value-of exp1 env store0) = (val1, store1)
(value-of exp2 env store1) = (val2, store2)
-------------------------------------------------------
(value-of (newpair-exp exp1 exp2) env store0)
= ((mutpair-val (pair l1 l2), [l2=val2][l1=val1]store2)

   
(value-of exp1 env store0) = ((mutpair-val (pair l1 l2)), store1)
-------------------------------------------------------
(value-of (left-exp exp1) = (store1(l1), store1)


(value-of exp1 env store0) = ((mutpair-val (pair l1 l2)), store1)
-------------------------------------------------------
(value-of (right-exp exp1) = (store1(l2), store1)

          
(value-of exp1 env store0) = ((mutpair-val (pair l1 l2)), store1)
(value-of exp2 env store1) = (val2, store2)
-------------------------------------------------------
(value-of (setleft-exp exp1 exp2) env store0)
= ((num-val 82), [l1=val2]store2)


          
(value-of exp1 env store0) = ((mutpair-val (pair l1 l2)), store1)
(value-of exp2 env store1) = (val2, store2)
-------------------------------------------------------
(value-of (setright-exp exp1 exp2) env store0)
= ((num-val 83), [l2=val2]store2)
|#