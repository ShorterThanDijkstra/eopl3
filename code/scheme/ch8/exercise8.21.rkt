#lang eopl
(require rackunit)
(require "PROC-MODULES.rkt")

(define ans
"
module double-ints-maker
   interface
     ((ints:  [opaque t
               zero : t
               succ : (t -> t)
               pred : (t -> t)
               is-zero : (t -> bool)])
      =>
      [opaque t
       zero: from ints take t
       succ: (from ints take t -> from ints take t)
       pred: (from ints take t -> from ints take t)
       is-zero: (from ints take t -> bool)
        ])
    body
      module-proc (ints : [opaque t
                            zero : t
                            succ : (t -> t)
                            pred : (t -> t)
                            is-zero : (t -> bool)])
      [type t = from ints take t
       zero = from ints take zero
       succ = let s = from ints take succ
                     in proc(x: t) (s (s x))
       pred = let p = from ints take pred
                    in proc(x: t) (p (p x))
       is-zero = from ints take is-zero
      ]
      
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
    
module ints-double
  interface
    [opaque t
    zero : from ints take t
    succ : (from ints take t -> from ints take t)
    pred : (from ints take t -> from ints take t)
    is-zero : (from ints take t -> bool)]
  body (double-ints-maker ints)

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
      
module ints-double-to-int
  interface [to-int : (from ints-double take t -> int)]
  body (to-int-maker ints-double)

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

module from-ints
   interface [from-int: (int -> from ints take t)]
   body (from-int-maker ints)

module from-ints-double
   interface [from-int: (int -> from ints-double take t)]
   body (from-int-maker ints-double)
     
let from-int = from from-ints take from-int
in let from-double-int = from from-ints-double take from-int
in let three1 = (from-int 3)
in let three2 = (from-double-int 3)
in let to-int1 = from ints-to-int take to-int
in let to-int2 = from ints-double-to-int take to-int
in -((to-int1 three1), (to-int2 three2))
")
; (:t ans) ; I don't know why does this fail