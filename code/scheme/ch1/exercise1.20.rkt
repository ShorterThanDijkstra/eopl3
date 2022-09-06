#lang eopl
(require rackunit)

;;; S-list ::= ()
;;;        ::= (Symbol . S-list)
;;;        ::= (S-list . S-list)

(define count-occurrences
  (lambda (s slist)
    (if (null? slist) 0
        (let [(first (car slist)) (rest (cdr slist))]
          (if (symbol? first)
              (if (eqv? first s)
                  (+ 1  (count-occurrences s rest))
                  (count-occurrences s rest))
              (+ (count-occurrences s first)
                 (count-occurrences s rest)))))))


(check-equal?
 (count-occurrences 'x '((f x) y (((x z) x))))
 3)

(check-equal?
 (count-occurrences 'x '((f x) y (((x z) () x))))
 3)

(check-equal?
 (count-occurrences 'w '((f x) y (((x z) x))))
 0)
