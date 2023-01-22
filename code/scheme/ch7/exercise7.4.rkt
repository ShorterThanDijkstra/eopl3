#lang eopl
#|
proc (x) x
(type-of <<x>> [x=t]tenv) = t
-----------------------------------
(type-of <<proc (x) x>> tenv) = (t -> t)

proc (x) proc (y) (x y) ;;; (ty -> t) -> (ty -> t)
(type-of <<(x y)>> [y=ty]tenv) = t
---------------------------------------------
(type-of <<x>> tenv) = (ty -> t)
---------------------------------------------
(type-of <<proc (y) (x y)>> [x=(ty -> t) tenv)
                    = (ty -> t)
---------------------------------------------
(type-of <<proc (x) proc (y) (x y)>> tenv) 
                    = (ty -> t) -> (ty -> t)
|#