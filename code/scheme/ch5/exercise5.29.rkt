#lang eopl
(define index 'uninitialized)
(define res 'uninitialized)

(define fact-iter
  (lambda (n)
    (set! index n)
    (set! res 1)
    (fact-iter-acc)
    res))

(define fact-iter-acc
  (lambda ()
    (if (zero? index)
        'return
        (begin  (set! res (* index res))
                (set! index (- index 1))
                (fact-iter-acc)))))