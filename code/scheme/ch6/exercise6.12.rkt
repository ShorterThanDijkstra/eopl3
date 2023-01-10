#lang eopl
#|
1. -((f -(x,1)),1)
No, (f -(x,1) is cps-call-exp
2. (f -(-(x,y),1))
No, it's cps-call-exp
3. if zero?(x) then -(x,y) else -(-(x,y),1)
Yes
4. let x = proc (y) (y x) in -(x,3)
No, it's cps-let-exp
5. let f = proc (x) x in (f 3)
No, it's cps-let-exp
|#