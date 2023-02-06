#lang eopl
#|
module ints
  interface
    [opaque t
     zero : t
     succ : (t -> t)
     pred : (t -> t)
     is-zero : (t -> bool)]
  body
     [type t = int
     zero = 3
     succ = proc(x : t) -(x, -5)
     pred = proc(x : t) -(x, 5)
     is-zero = proc (x : t) zero?(-(x, 3))]
  let z = from ints take zero
  in let s = from ints take succ
  in let p = from ints take pred
  in let z? = from ints take is-zero
  in letrec int to-int (x : from ints take t) =
                  if (z? x)
                  then 0
                  else -((to-int (p x)), -1)
  in (to-int (s (s z)))
|#