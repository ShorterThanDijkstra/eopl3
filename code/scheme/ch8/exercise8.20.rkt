#lang eopl
(require rackunit)
(require "PROC-MODULES.rkt")

(define ans
"
module ints
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

module sum-prod-maker
  interface
    ((ints : [opaque t
              zero : t
              succ : (t -> t)
              pred : (t -> t)
              is-zero : (t -> bool)])
    => [plus : (from ints take t
                -> (from ints take t
                   -> from ints take t))
       times : (from ints take t
                -> (from ints take t
                   -> from ints take t))])
  body
    module-proc (ints : [opaque t
                         zero : t
                         succ : (t -> t)
                         pred : (t -> t)
                         is-zero : (t -> bool)])
   [plus =  let z = from ints take zero
            in let s = from ints take succ
               in let p = from ints take pred
                  in let z? = from ints take is-zero
                     in letrec (from ints take t -> from ints take t) plus1 (a: from ints take t)
                               = proc(b: from ints take t)
                                    if (z? a)
                                    then b
                                    else (s ((plus1 (p a)) b))
                        in plus1
    times =  let z = from ints take zero
             in let s = from ints take succ
                in let p = from ints take pred
                   in let z? = from ints take is-zero
                      in letrec (from ints take t -> from ints take t) times1(a: from ints take t)
                                = proc(b: from ints take t)
                                    if (z? a)
                                    then z
                                    else let temp = ((times1 (p a)) b)
                                        in ((plus temp) b)
                         in times1
    ]

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
                                                            
module ints-to-int
  interface [to-int : (from ints take t -> int)]
  body (to-int-maker ints)
                                                            
module from-ints
   interface [from-int: (int -> from ints take t)]
   body (from-int-maker ints)

module sum-prod
   interface [plus : (from ints take t
                -> (from ints take t
                   -> from ints take t))
              times : (from ints take t
                       -> (from ints take t
                          -> from ints take t))]
    body (sum-prod-maker ints)
                                                                                                                                                   
let to-int  = from ints-to-int take to-int
in let from-int = from from-ints take from-int                                                                                                                      
in let plus = from sum-prod take plus
in let times = from sum-prod take times
in let a = (from-int 37)
in let b = (from-int 73)
in let sum = ((plus a) b)
in let prod = ((times sum) sum)
in (to-int prod) %expect to be 12100                                                            
                                                           
")
(check-equal? (:t ans) 'int)
(check-equal? (:e ans) (num-val 12100))