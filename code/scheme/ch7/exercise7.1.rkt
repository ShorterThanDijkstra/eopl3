#lang eopl
#|
1. proc (x) -(x,3)
Int -> Int

2. proc (f) proc (x) -((f x), 1)
(t -> Int) -> (t -> Int)

3. proc (x) x
t
4. proc (x) proc (y) (x y)
(t1 -> t2) -> (t1 -> t2)

5. proc (x) (x 3)
(Int -> t) -> Int

6. proc (x) (x x)
(t1 -> t2)
((t1 -> t2) -> t2)
...
no type

7. proc (x) if x then 88 else 99
t -> Int

8. proc (x) proc (y) if x then y else 99
t -> (Int -> Bool)

9.(proc (p) if p then 88 else 99
  33)
Type error

10. (proc (p) if p then 88 else 99
     proc (z) z)
Type error

11. proc (f)
      proc (g)
        proc (p)
          proc (x) if (p (f x)) then (g 1) else -((f x),1)
(tx -> Int) -> ((Int -> Int) -> ((Int -> Bool) -> (tx -> Int)))

12. proc (x)
      proc(p)
        proc (f)
          if (p x) then -(x,1) else (f p)
Int -> ((Int -> Bool) -> (((Int -> Bool) -> Int) -> Int)))

13. proc (f)
      let d = proc (x)
                proc (z) ((f (x x)) z)
      in proc (n) ((f (d d)) n)
no type, I think
|#
