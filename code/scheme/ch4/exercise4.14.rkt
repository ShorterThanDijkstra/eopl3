#lang eopl
; (value-of exp1 env store0) = (val1, store1)
; ---------------------------------------------
; (value-of (let-exp var exp1 body) env store0)
; = (value-of body env [l=val]store1)