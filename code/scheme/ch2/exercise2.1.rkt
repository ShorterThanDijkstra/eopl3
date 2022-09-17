#lang eopl
(require rackunit)

(define N 1073741824)

(define zero (lambda () '(0)))
(define is-zero? (lambda (n) (equal? n '(0))))
(define successor
  (letrec [(carry-go
            (lambda (loi carry)
              (if (null? loi)
                  (if (= carry 1) '(1) '())
                  (let [(first (+  (car loi) carry))
                        (rest (cdr loi))]
                    (if (= N first)
                        (cons 0 (carry-go rest 1))
                        (cons first rest))))))]
    (lambda (n)
      (if (null? n)
          (eopl:error "invalid input")
          (carry-go n 1)))))

(define predecessor
  (letrec [(carry-go
            (lambda (loi carry)
              (if (null? loi) '()
                  (let [(first (+ (car loi) carry))
                        (rest (cdr loi))]
                    (if (= first -1)
                        (cons (- N 1) (carry-go rest -1))
                        (cons first rest))))))]
    (lambda (n)
      (if (or (null? n) (equal? n '(0)))
          (eopl:error "invalid input")
          (carry-go n -1)))))

(define one (successor (zero)))
(define add
  (lambda (m n)
    (cond [(is-zero? m) n]
          [(is-zero? n) m]
          [else (successor (add (predecessor m) n))])))
(define mul
  (lambda (m n)
    (cond [(is-zero? m) (zero)]
          [(is-zero? n) (zero)]
          [(is-zero? (predecessor m)) n]
          [(is-zero? (predecessor n)) m]
          [else (add n (mul (predecessor m) n))])))

(define factorial
  (lambda (n)
    (if (is-zero? n) one
        (mul n (factorial (predecessor n))))))

;;; test
(define (bigits->natural-number loi)
  (letrec [(go (lambda (loi index)
                 (if (null? loi) 0
                     (+ (* (car loi) (expt N index))
                        (go (cdr loi) (+ index 1))))))]
    (go loi 0)))

(define (natural-number->bigits num)
  (if (= num 0)
      (zero)
      (successor (natural-number->bigits (- num 1)))))


(check-equal? (is-zero? (zero)) #t)
(check-equal? (is-zero? (successor (zero))) #f)
(check-equal? (is-zero? (predecessor (successor (zero)))) #t)

(define MAX 999999)

(define (check-successor bigit index)
  (cond [(= index MAX) #t]
        [(= (bigits->natural-number bigit) index)
         (check-successor (successor bigit) (+ index 1))]
        [else #f]))
(check-equal? (check-successor (zero) 0) #t)

(define (check-predecessor bigit index)
  (cond [(= index 0) #t]
        [(= (bigits->natural-number bigit) index)
         (check-predecessor (predecessor bigit) (- index 1))]
        [else #f]))
(check-equal? (check-predecessor (natural-number->bigits MAX) MAX) #t)

(check-equal? (factorial (natural-number->bigits 10)) (natural-number->bigits 3628800))