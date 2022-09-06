#lang eopl
(require rackunit)

(define (merge loi1 loi2)
  (cond [(null? loi1) loi2]
        [(null? loi2) loi1]
        [else (let [(i1 (car loi1)) (i2 (car loi2))]
                (if (< i1 i2) (cons i1 (merge (cdr loi1) loi2))
                    (cons i2 (merge loi1 (cdr loi2)))))]))

;;; contract: list of list -> list of list (length is 1)
(define (merge-sort lolst)
  (cond [(null? lolst) '()]
        [(null? (cdr lolst)) lolst]
        [else (let [(sorted (merge-sort (cddr lolst)))
                    (merged (merge (car lolst) (cadr lolst)))]
                (merge-sort (cons merged sorted)))]))

(define (sort loi)
  (car (merge-sort (map list loi))))


(check-equal?  (sort '(8 2 5 2 3)) '(2 2 3 5 8))