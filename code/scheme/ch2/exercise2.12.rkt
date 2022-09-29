#lang eopl
(require rackunit)

; (empty-stack) = []

; (push [ ... ] val) = [val...]

; (pop [val ...]) = [...]

; (top [val ... ]) = val

; (empty-stack? []) = #t
; (empty-stack? [...]) = #f

(define top
  (lambda (stack)
    (stack 'top)))

(define pop
  (lambda (stack)
    (stack 'pop)))


(define empty-stack?
  (lambda (stack)
    (stack 'empty?)))

(define empty-stack
  (lambda ()
    (lambda (op)
      (cond [(eqv? op 'pop) (eopl:error "error")]
            [(eqv? op 'top) '()]
            [(eqv? op 'empty?) #t]
            [else (eopl:error "error")]))))

(define push
  (lambda (stack val)
    (lambda (op)
      (cond [(eqv? op 'pop) stack]
            [(eqv? op 'top) val]
            [(eqv? op 'empty?) #f]
            [else (eopl:error "error")]))))

;;; test

(define stack1
  (push (empty-stack) 1))

(check-equal? (top stack1) 1)
(check-equal? (empty-stack? stack1) #f)
(check-equal? (empty-stack? (pop stack1)) #t)

(define stack2
  (push stack1 2))

(check-equal? (top stack2) 2)
(check-equal? (empty-stack? (pop (pop stack2)))  #t)