#lang eopl
#|
module double-maker
   interface
     ((ints:  [opaque t
               zero : t
               succ : (t -> t)
               pred : (t -> t)
               is-zero : (t -> bool)])
      =>
      [zero: from ints take t
       succ: (from ints take t) -> (from ints take t)
       pred: (from ints take t) -> (from ints take t)
       is-zero: (from ints take t -> bool)
        ]
    body
      (module-proc (ints : [opaque t
                            zero : t
                            succ : (t -> t)
                            pred : (t -> t)
                            is-zero : (t -> bool)])
      [zero = from ints take zero
       succ = let s = from ints take succ
                     in proc(x: from ints take t) (s (s x))
       pred = let p = from ints take pred
                    in proc(x: from ints take t) (p (p x))
       is-zero = from ints take is-zero
      ])
                   
|#