#lang eopl
(require rackunit)

(define (merge pred loi1 loi2)
  (cond [(null? loi1) loi2]
        [(null? loi2) loi1]
        [else (let [(i1 (car loi1)) (i2 (car loi2))]
                (if (pred i1 i2) (cons i1 (merge pred (cdr loi1) loi2))
                    (cons i2 (merge pred loi1 (cdr loi2)))))]))

(define (merge-sort pred lolst)
  (cond [(null? lolst) '()]
        [(null? (cdr lolst)) lolst]
        [else (let [(sorted (merge-sort pred (cddr lolst)))
                    (merged (merge pred (car lolst) (cadr lolst)))]
                (merge-sort pred (cons merged sorted)))]))

(define (sort/predicate pred loi)
  (car (merge-sort pred (map list loi))))


(check-equal?  (sort/predicate < '(8 2 5 2 3)) '(2 2 3 5 8))
(check-equal?  (sort/predicate > '(8 2 5 2 3)) '(8 5 3 2 2))
