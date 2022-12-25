#lang racket
(let ([f
       (lambda (f)
         (f f))])
  (f f))

(let ([make-factorial
       (lambda (maker)
         (lambda (n)
           (if (= n 0)
               1
               (* ((maker maker) (- n 1)) n))))])
  (let ([factorial (make-factorial make-factorial)])
    (factorial 10)))


; (let ([make-rec
;        (lambda (f)
;          (let ([maker
;                 (lambda (maker)
;                   (f (maker maker)))])
;                (maker maker)))])
;       (let ([factorial
;              (lambda (f)
;                (lambda (n)
;                  (if (= 0 n)
;                      1
;                      (* (f (- n 1)) n))))])
;         ((make-rec factorial) 10)))


(let ([make-rec
       (lambda (f)
         (let ([maker
                (lambda (maker)
                  (lambda (x)
                    ((f (maker maker)) x)))])
           (maker maker)))])
  (let ([factorial
         (lambda (f)
           (lambda (n)
             (if (= 0 n)
                 1
                 (* (f (- n 1)) n))))])
    ((make-rec factorial) 10)))


; (let ([make-rec
;        (lambda (f)
;          (let ([maker
;                 (lambda (maker)
;                   (lambda (x)
;                     ((f (maker maker)) x)))])
;            (f (maker maker))))])
;   (let ([factorial
;          (lambda (f)
;            (lambda (n)
;              (if (= 0 n)
;                  1
;                  (* (f (- n 1)) n))))])
;     ((make-rec factorial) 10)))

; (define Y
;   (lambda (f)
;     ((lambda (maker)
;        (f (maker maker)))
;      (lambda (maker)
;        (lambda (x)
;          ((f (maker maker)) x))))))

(let ([make-rec
       (lambda (f)
         (let ([maker
                (lambda (maker)
                  (lambda (x)
                    ((f (maker maker)) x)))])
           (maker maker)))])
  (let ([fib
         (lambda (f)
           (lambda (n)
             (if (< n 2)
                 n
                 (+ (f (- n 1)) (f (- n 2))))))])
    ((make-rec fib) 20)))

(define Y0
  (lambda (f)
    ((lambda (maker)
       (maker maker))
     (lambda (maker)
       (lambda (x)
         ((f (maker maker)) x))))))

