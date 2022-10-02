#lang eopl

; Lc-exp ::= (var Identifier)
;        ::= (lambda Identifier Lc-exp)
;        ::= (app Lc-exp Lc-exp)

; Lc-exp ::= Identifier
;        ::= (-> Identifier Lc-exp)
;        ::= (: Lc-exp Lc-exp)