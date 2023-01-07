#lang eopl
#|
1. (lambda (x y) (p (+ 8 x) (q y)))

(lambda (x y k) (q y (lambda (v0)
                       (p (+ 8 x) v0 k))))


2. (lambda (x y u v) (+ 1 (f (g x y) (+ u v))))


(lambda (x y u v k) (g x y (lambda (v0)
                           (f v0 (+ u v) (lambda (v1)
                                           (k (+ 1 v1)))))))


3. (+ 1 (f (g x y) (+ u (h v))))

(h v (lambda (v0)
       (g x y (lambda (v1)
                (f v1 (+ u v0) (lambda (v2)
                                 (+ 1 v2)))))))


4. (zero? (if a (p x) (p y)))

(p x (lambda (v0)
       (p y (lambda (v1)
              (zero? (if a v0 v1))))))


5. (zero? (if (f a) (p x) (p y)))


(f a (lambda (v0)
       (p x (lambda (v1)
              (p y (lambda v2)
                 (zero? (if v0 v1 v2)))))))

6. (let ((x (let ((y 8)) (p y)))) x)

(let ((y 8))
  (p y (lambda (v0)
         (let ((x v0))
           x))))


7. (let ((x (if a (p x) (p y)))) x)

(p x (lambda (v0)
       (p y (lambda (v1)
              (let ((x (if a v0 v1)))
                x)))))
|#
