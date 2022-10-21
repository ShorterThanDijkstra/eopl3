#lang racket
(let ([make-factorial
       (lambda (maker)
         (lambda (n)
           (if (= n 0)
               1
               (* ((maker maker) (- n 1)) n))))])
      (let ([factorial (make-factorial make-factorial)])
        (factorial 10)))