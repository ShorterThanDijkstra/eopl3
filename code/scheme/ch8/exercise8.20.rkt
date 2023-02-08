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
                                    let temp = ((times1 (p a)) b)
                                        in ((plus temp) b)
                                   in times2
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
                                                 else (succ (from-int -(i, 1))
                                                            
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

let to-int  = from (to-int-maker ints) take to-int
in let from-int = from (from-int-maker ints) take from-int                                                                                                                      
in let plus = from (sum-prod-maker ints) take plus
in let times = from (sum-prod-maker ints) take times
in let a = (from-int 37)
in let b = (from-int 73)
in let c = let sum = ((plus a) b)
           in let prod = ((time sum) sum)
              in (to-int prod) %expect to be 12100                                                            
                                                           
|#