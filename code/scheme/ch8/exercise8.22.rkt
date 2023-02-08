#lang eopl
#|
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
             let z? = from ints take is-zero
             in letrec (from ints take t -> bool) equal(a: from ints take t)
                       = proc(b: from ints take t)
                           if (z? a)
                           then (z? b)
                           else let a1 = (p a)
                                in let b1 = (p b)
                                   in ((equal a1) b1)
                in equal])
|#