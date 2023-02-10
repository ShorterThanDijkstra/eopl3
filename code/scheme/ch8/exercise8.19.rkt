#lang eopl
(require rackunit)
(require "PROC-MODULES.rkt")

(define ans
"
module ints1
  interface
    [opaque t
    zero : t
    succ : (t -> t)
    pred : (t -> t)
    is-zero : (t -> bool)]
  body
    [type t = int
    zero = 0
    succ = proc(x : t) -(x,-5)
    pred = proc(x : t) -(x,5)
    is-zero = proc (x : t) zero?(x)]

module ints2
  interface
    [opaque t
    zero : t
    succ : (t -> t)
    pred : (t -> t)
    is-zero : (t -> bool)]
  body
    [type t = int
    zero = 0
    succ = proc(x : t) -(x,3)
    pred = proc(x : t) -(x,-3)
    is-zero = proc (x : t) zero?(x)]

module to-int-maker
  interface
    ((ints : [opaque t
              zero : t
              succ : (t -> t)
              pred : (t -> t)
              is-zero : (t -> bool)])
    => [to-int : (from ints take t -> int)])
  body
    module-proc (ints : [opaque t
                         zero : t
                         succ : (t -> t)
                         pred : (t -> t)
                         is-zero : (t -> bool)])
    [to-int
        = let z? = from ints take is-zero
          in let p = from ints take pred
             in letrec int to-int (x : from ints take t)
                             = if (z? x)
                             then 0
                             else -((to-int (p x)), -1)
             in to-int]

module ints1-to-int
  interface [to-int : (from ints1 take t -> int)]
  body (to-int-maker ints1)
module ints2-to-int
  interface [to-int : (from ints2 take t -> int)]
  body (to-int-maker ints2)

module from-int-maker
  interface
    ((ints : [opaque t
              zero : t
              succ : (t -> t)
              pred : (t -> t)
              is-zero : (t -> bool)])
    => [from-int : (int -> from ints take t)])
body
   module-proc (ints : [opaque t
                         zero : t
                         succ : (t -> t)
                         pred : (t -> t)
                         is-zero : (t -> bool)])
   [from-int = let succ = from ints take succ
               in let zero = from ints take zero
                  in letrec from ints take t from-int(i: int)
                                               = if zero?(i)
                                                 then zero
                                                 else (succ (from-int -(i, 1)))
                      in from-int]

module from-ints1
   interface [from-int: (int -> from ints1 take t)]
   body (from-int-maker ints1)

module from-ints2
   interface [from-int: (int -> from ints2 take t)]
   body (from-int-maker ints2)
                                                                                                                                                                                                                                                                                                      
let from-int1 = from from-ints1 take from-int
in let from-int2 = from from-ints2 take from-int                                                           
in let two1 = (from-int1 2) %from ints1 take t
in let two2 = (from-int2 2) %from ints2 take t
in let to-ints1 = from ints1-to-int take to-int
in let to-ints2 = from ints2-to-int take to-int
in -((to-ints1 two1), (to-ints2 two2))
")
(check-equal? (:t ans) 'int)
(check-equal? (:e ans) (num-val 0))
