#lang eopl
#|
(let-exp var rhs body) : t_var = t_rhs
                         t_body = t_(let-exp var rhs body)

1. let x = 4 in (x 3)
error

2. let f = proc (z) z in proc (x) -((f x), 1)
tf = tx -> int
tf = tz -> tz
tx = int

answer: int -> int

3. let p = zero?(1) in if p then 88 else 99
int

4. let p = proc (z) z in if p then 88 else 99
error
|#
