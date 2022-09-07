#lang eopl
(require rackunit)

; Binary-search-tree ::= () | (Int Binary-search-tree Binary-search-tree)
(define (traverse n bst path-reverse)
  (cond [(null? bst) path-reverse]
        [(= n (car bst)) path-reverse]
        [(< n (car bst)) (traverse n (cadr bst) (cons 'left path-reverse))]
        [else (traverse n (caddr bst) (cons 'right path-reverse))]))

(define (path n bst)
  (reverse (traverse n bst '())))

;;; test
(check-equal? (path 17 '(14 (7 () (12 () ()))
                            (26 (20 (17 () ())
                                    ())
                                (31 () ()))))
              '(right left left))