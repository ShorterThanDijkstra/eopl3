#lang eopl
(require rackunit)

;;; parent ::= (Int is-left-son? sibling)
;;; ancestors ::= (list parent)
;;; bintree ::= (Int ancestors child child)
;;; child :== (Int child child)
;;; leaf :: ('() ancestors '() '()) | '()

(define (number->bintree num)
  (list num '() '() '()))

(define (at-root? bintree)
  (null? (cadr bintree)))

(define (at-leaf? bintree)
  (or (null? bintree)
      (null? (car bintree))))

(define (current-element bintree)
  (car bintree))

(define (move-to-left-son bintree)
  (if (at-leaf? bintree)
      (eopl:error "error")
      (let ([root-val (car bintree)]
            [ancestors (cadr bintree)]
            [left-son (caddr bintree)] ; (num left right)
            [right-son (cadddr bintree)])
        (let ([parent (list root-val #t right-son)])
          (let ([new-ancestors (cons parent ancestors)])
            (if (null? left-son)
                (list '() new-ancestors '() '())
                (let ([new-root-val (car left-son)]
                      [new-children (cdr left-son)])
                  (cons new-root-val (cons new-ancestors new-children)))))))))

(define (move-to-right-son bintree)
  (if (at-leaf? bintree) ; can not move
      (eopl:error "error")
      (let ([root-val (car bintree)]
            [ancestors (cadr bintree)]
            [left-son (caddr bintree)]
            [right-son (cadddr bintree)])
        (let ([parent (list root-val #f left-son)])
          (let ([new-ancestors (cons parent ancestors)])
            (if (null? right-son)
                (list '() new-ancestors '() '()) ; leaf
                (let ([new-root-val (car right-son)]
                      [new-children (cdr right-son)])
                  (cons new-root-val (cons new-ancestors new-children)))))))))

(define (move-up bintree)
  (let ([root-val (car bintree)]
        [ancestors (cadr bintree)]
        [left-son (caddr bintree)]
        [right-son (cadddr bintree)])
    (let ([new-son (if (null? root-val) '() (list root-val left-son right-son))]
          [parent (car ancestors)]
          [new-ancestors (cdr ancestors)])
      (let ([new-root-val (car parent)]
            [is-left-son (cadr parent)]
            [sibling (caddr parent)])
        (if is-left-son
            (list new-root-val new-ancestors new-son sibling)
            (list  new-root-val new-ancestors sibling new-son))))))

(define (insert-to-left num bintree)
  (let ([root-val (car bintree)]
        [ancestors (cadr bintree)]
        [left-son (caddr bintree)]
        [right-son (cadddr bintree)])
    (list root-val ancestors (list num left-son '()) right-son)))

(define (insert-to-right num bintree)
  (let ([root-val (car bintree)]
        [ancestors (cadr bintree)]
        [left-son (caddr bintree)]
        [right-son (cadddr bintree)])
    (list root-val ancestors left-son (list num '() right-son))))


(define t0 (number->bintree 13))
(check-equal? (at-leaf? (move-to-left-son t0)) #t)
(check-equal? (at-root? t0) #t)

(define t1 (insert-to-left 12 t0))
(check-equal? (at-leaf? (move-to-right-son t1)) #t)
(check-equal? (at-root? t1) #t)

(define t2 (insert-to-right 14 t1))
(check-equal? (at-leaf? t2) #f)
(check-equal? (at-root? t2) #t)

(define t3 (insert-to-left 11 t2))

(check-equal? (move-up (move-up (move-to-left-son (move-to-left-son t3)))) t3)
(check-equal? (move-up (move-to-right-son t3)) t3)
(check-equal? (move-up (move-to-left-son (move-to-left-son t3))) (move-to-left-son t3))


