#lang eopl
; (value-of exp1 env store0) = (val1, store1)
; -----------------------------------------------------------------------------------------
; (value-of zero?-exp(exp1) env store0) = ((bool-val #t), store1) if (expval-num val1) = 0
;                                       = ((bool-val #f), store1) if (expval-num val1) != 0