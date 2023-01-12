#lang eopl
(require racket/trace)

(define (=c x y k)
  (k (= x y)))

(define (<c x y k)
  (k (< x y)))

(define (-c x y k)
  (k (- x y)))

(define (*c x y k)
  (k (* x y)))

(define (+c x y k)
  (k (+ x y)))

(define (/c x y k)
  (k (/ x y)))

(define (append-c x y k)
  (k (append x y)))

(define (id x)
  x)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (recsum n)
  (if (= n 0) 0 (+ n (recsum (- n 1)))))

(define (recsum/k n k)
  (=c n
      0
      (lambda (b)
        (if b
            (k 0)
            (-c n 1 (lambda (v1) (recsum/k v1 (lambda (v2) (+c n v2 k)))))))))

(trace recsum/k)
(trace recsum)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (fact n)
  (if (= n 0) 1 (* n (fact (- n 1)))))

(define (fact/k n k)
  (=c n
      0
      (lambda (v0)
        (if v0
            (k 1)
            (-c n 1 (lambda (v1) (fact/k v1 (lambda (v2) (*c n v2 k)))))))))
(trace fact/k)
(trace fact)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (fib n)
  (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))

(define (fib/k n k)
  (<c n
      2
      (lambda (v0)
        (if v0
            (k n)
            (-c n
                1
                (lambda (v1)
                  (fib/k v1
                         (lambda (v2)
                           (-c n
                               2
                               (lambda (v3)
                                 (fib/k v3 (lambda (v4) (+c v2 v4 k)))))))))))))

(trace fib/k)
(trace fib)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (move a c)
  (list (list a '-> c)))

(define (hanoi n a b c)
  (if (= n 1)
      (move a c)
      (append (hanoi (- n 1) a c b) (move a c) (hanoi (- n 1) b a c))))

#|
(define (hanoi/k n a b c k)
  ((lambda (x y k) (k (= x y)))
   n
   1
   (lambda (v0)
     (if v0
         (k (move a c))
         ((lambda (x y k) (k (- x y)))
          n
          1
          (lambda (v1)
            (hanoi/k v1
                     a
                     c
                     b
                     (lambda (v2)
                       ((lambda (x y k) (k (append x y)))
                        v2
                        (move a c)
                        (lambda (v3)
                          (hanoi/k v1
                                   b
                                   a
                                   c
                                   (lambda (v4)
                                     ((lambda (x y k) (k (append x y))) v3 v4 k)))))))))))))
|#
(define (move/k a c k)
  (k (list (list a '-> c))))
(define (hanoi/k n a b c k)
  (if (= n 1)
      (k (move a c))
      (hanoi/k
       (- n 1)
       a
       c
       b
       (lambda (v0)
         (move/k
          a
          c
          (lambda (v1)
            (hanoi/k (- n 1) b a c (lambda (v2) (k (append v0 v1 v2))))))))))
(trace hanoi)
(trace hanoi/k)

(lambda (f) (lambda (x) (f x)))

(lambda (f k) (k (lambda (x k) (f x k))))

(lambda (f) (lambda (x) (if (< x 2) x (+ (f (- x 1)) (f (- x 2))))))

; (lambda (f k)
;   (lambda (x k)
;     (if (< x 2)
;         (k x)
;         (f (- x 1) (lambda (v0) (f (- x 2) (lambda (v1) (k (+ v0 v1)))))))))

(lambda (f k)
  (k (lambda (x k)
       (if (< x 2)
           (k x)
           (f (- x 1)
              (lambda (v0)
                (f (- x 2)
                   (lambda (v1)
                     (k (+ v0 v1))))))))))
