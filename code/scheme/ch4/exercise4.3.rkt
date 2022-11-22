#lang eopl
; (value-of rator env store0) = (prcc, store1)
; (value-of rand  env store1) = (arg, store2)
; -----------------------------------------------------------------------------------------
; (value-of  (call-exp (rator rand)) env store0)
;            = (apply-procedure proc arg store2)
