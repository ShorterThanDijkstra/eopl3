#lang eopl
(require rackunit)
(require "PROC-MODULES.rkt")

(define ans
"
module equality-maker
  interface
    ((ints : [opaque t
              zero : t
              succ : (t -> t)
              pred : (t -> t)
              is-zero : (t -> bool)])
    => [equal : (from ints take t
                 -> (from ints take t
                    -> bool))])
  body
    module-proc (ints : [opaque t
                           zero : t
                           succ : (t -> t)
                           pred : (t -> t)
                           is-zero : (t -> bool)])
    [equal = let p = from ints take pred
             in let z? = from ints take is-zero
             in letrec (from ints take t -> bool) equal(a: from ints take t)
                       = proc(b: from ints take t)
                           if (z? a)
                           then (z? b)
                           else let a1 = (p a)
                                in let b1 = (p b)
                                   in ((equal a1) b1)
                in equal]

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

module equality-ints
  interface [equal : (from ints take t
                 -> (from ints take t
                    -> bool))]
  body (equality-maker ints)
  
let s = from ints take succ
in let z = from ints take zero
in let three = (s (s (s z)))
in let five = (s (s (s (s (s z)))))
in let equal = from equality-ints take equal
in let p = from ints take pred
in ((equal (p (p five))) (p three))
")
(check-equal? (:t ans) 'bool)
(check-equal? (:e ans) (bool-val #f))