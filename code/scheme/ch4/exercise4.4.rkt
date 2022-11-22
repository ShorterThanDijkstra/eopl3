#lang eopl
; (value-of exp1 env store0) = (val1, store1)
; (value-of exp2 env store1) = (val2, store2)
; ...
; (value-of expN env storeN-1) = (valN, storeN)
; -----------------------------------------------------------------------------------------
; (value-of  (begin (exp1 exp2 ... epxN)) env store0) = (valN, storeN)
