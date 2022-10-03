#lang eopl
(require rackunit)


(define-datatype Stack stack?
  (Empty-stack)
  (Push (saved-stack stack?) (val always?)))

(define (top stack)
  (cases Stack stack
    [Empty-stack () '()]
    [Push (saved-stack val) val]))

(define (pop stack)
  (cases Stack stack
    [Empty-stack () (eopl:error "error")]
    [Push (saved-stack val) saved-stack]))

(define (empty-stack? stack)
  (cases Stack stack
    [Empty-stack () #t]
    [Push (saved-stack val) #f]))


;;; test
(define stack1
  (Push (Empty-stack) 1))

(check-equal? (top stack1) 1)
(check-equal? (empty-stack? stack1) #f)
(check-equal? (empty-stack? (pop stack1)) #t)

(define stack2
  (Push stack1 2))

(check-equal? (top stack2) 2)
(check-equal? (empty-stack? (pop (pop stack2)))  #t)
