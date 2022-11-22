#lang eopl
; (value-of exp1 env store0) = (l, store1)
; (value-of exp2 env store1) = (val, store2)
; --------------------------------------------------------------------
; (value-of (setref-exp exp1 exp2) env store0) = (val ,[l=val]store2 )