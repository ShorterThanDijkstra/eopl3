#lang eopl
#|
(letrec-exp
    p-result-types
    p-names
    b-vars
    b-vars-types
    p-bodies
    letrec-body)
    = t_p-names[0] = t_b-vars-types[0] -> t_p-bodies[0]
    = t_p-names[1] = t_b-vars-types[1] -> t_p-bodies[1]
    ...
    = t_p-names[n] = t_b-vars-types[n] -> t_p-bodies[n]
    t_letrec-exp = t_letrec-body

1. letrec ? f (x : ?)
        = if zero?(x) then 0 else -((f -(x,1)), -2)
   in f
tx = int
tf = int -> int

answer: int -> int


2. letrec ? even (x : ?)
             = if zero?(x) then 1 else (odd -(x,1))
          ? odd (x : ?)
             = if zero?(x) then 0 else (even -(x,1))
   in (odd 13)

tx = int
todd = int -> int
teven = int -> int

answer: int 


3. letrec ? even (odd : ?)
             = proc (x) if zero?(x)
                        then 1
                        else (odd -(x,1))
   in letrec ? odd (x : ?) =
                if zero?(x)
                then 0
                else ((even odd) -(x,1))
      in (odd 13)

todd = int -> int
tx = int
teven = (int -> int) -> (int -> int)

answer: int
|#
