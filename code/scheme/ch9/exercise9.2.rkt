#lang eopl

(require "CLASSES.rkt")
(require rackunit)

(define ans
  "class oddeven extends object 
     method initialize() 1
     method even(n) if zero?(n) then 1 else send self odd (-(n,1))
     method odd(n) if zero?(n) then 0 else send self even (-(n,1))
  
   class bogus-oddeven extends oddeven
     method initialize() 3
     method even(n) zero?(1)
   let o1 = new bogus-oddeven()
   in send o1 odd(13)")
 