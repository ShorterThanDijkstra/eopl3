#lang racket
(require racket/trace)

(define fib
  (lambda (n)
    (if (< n 2)
        n
        (+ (fib (- n 1)) (fib (- n 2))))))

(define fib/cps
  (lambda (n k)
    (if (< n 2)
        (k n)
        (fib/cps (- n 1)
                 (lambda (v0)
                   (fib/cps (- n 2)
                            (lambda (v1)
                              (k (+ v0 v1)))))))))                         

(define fib/anf
  (lambda (n)
    (if (< n 2)
        n
        (let ((val1 (fib/anf (- n 1)))
              (val2 (fib/anf (- n 2))))
          (+ val1 val2)))))

; (trace fib/anf)
; (trace fib/cps)


(let ((x (cos (cos pi))))
  x)

(let ((var0 (cos pi)))
  (let ((x (cos var0)))
    x))  
