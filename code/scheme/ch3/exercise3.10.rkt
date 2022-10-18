#lang eopl
(require "let-interpreter.rkt")
(require rackunit)


(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (list-val (lst list?)))

(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
                	variant value)))

(define expval->num
  (lambda (v)
    (cases expval v
      	(num-val (num) num)
      	(else (expval-extractor-error 'num v)))))

(define expval->bool
  (lambda (v)
    (cases expval v
      	(bool-val (bool) bool)
      	(else (expval-extractor-error 'bool v)))))

(define expval->list
  (lambda (v)
    (cases expval v
      	(list-val (lst) lst)
      	(else (expval-extractor-error 'lst v)))))

(define expval->scheme-val
  (lambda (v)
    (cases expval v
      (num-val (num) num)
      (bool-val (bool) bool)
      (list-val (lst) lst))))

(define expval-constructor-error
  (lambda (value)
    (eopl:error 'scheme-val->expval "Bad Scheme Value" value)))

(define scheme-val->expval
  (lambda (sv)
    (cond [(number? sv) (num-val sv)]
          [(boolean? sv) (bool-val sv)]
          [(list? sv) (list-val sv)]
          [else (expval-constructor-error sv)])))

(define-datatype expression expression?
  (const-exp
   (num number?))
  (cons-exp
   (exp1 expression?)
   (exp2 expression?))
  (car-exp
   (exp1 expression?))
  (cdr-exp
   (exp2 expression?))
  (null?-exp
   (exp1 expression?))
  (emptylist-exp)
  (list-exp
   (exps (list-of expression?)))
  (diff-exp
   (exp1 expression?)
   (exp2 expression?))
  (minus-exp
   (exp1 expression?))
  (zero?-exp
   (exp1 expression?))
  (if-exp
   (exp1 expression?)
   (exp2 expression?)
   (exp3 expression?))
  (equal?-exp
   (exp1 expression?)
   (exp2 expression?))
  (greater?-exp
   (exp1 expression?)
   (exp2 expression?))
  (less?-exp
   (exp1 expression?)
   (exp2 expression?))
  (var-exp
   (var identifier?))
  (add-exp
   (var1 expression?)
   (var2 expression?))
  (mul-exp
   (var1 expression?)
   (var2 expression?))
  (quotient-exp
   (var1 expression?)
   (var2 expression?))
  (let-exp
   (var identifier?)
   (exp1 expression?)
   (body expression?)))

; value-of : Exp × Env → ExpVal
(define value-of
  (lambda (exp env)
    (cases expression exp

      (const-exp (num) (num-val num))
      (cons-exp (exp1 exp2)
                (let ([val1 (value-of exp1 env)]
                      [val2 (value-of exp2 env)])
                  (list-val (cons (expval->scheme-val val1) (expval->list val2)))))
      (car-exp (exp1)
               (scheme-val->expval (car (expval->list (value-of exp1 env)))))
      (cdr-exp (exp1)
               (scheme-val->expval (cdr (expval->list (value-of exp1 env)))))
      (null?-exp (exp1)
                 (bool-val (null? (expval->list (value-of exp1 env)))))
      (emptylist-exp ()
                     (scheme-val->expval '()))
      ; list-val
      (list-exp (exps)
                (list-val
                 (map (lambda (ev) (expval->scheme-val ev)) ; list of scheme values
                      (map (lambda (exp) (value-of exp env)) exps)))) ; list of expval
      (var-exp (var) (apply-env env var))

      (diff-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                    (num-val
                     (- num1 num2)))))
      (minus-exp (exp1)
                 (num-val (- 0 (expval->num (value-of exp1 env)))))
      (add-exp (exp1 exp2)
               (let ([val1 (value-of exp1 env)]
                     [val2 (value-of exp2 env)])
                 (num-val (+ (expval->num val1) (expval->num val2)))))
      (mul-exp (exp1 exp2)
               (let ([val1 (value-of exp1 env)]
                     [val2 (value-of exp2 env)])
                 (num-val (* (expval->num val1) (expval->num val2)))))
      (quotient-exp (exp1 exp2)
                    (let ([val1 (value-of exp1 env)]
                          [val2 (value-of exp2 env)])
                      (num-val (quotient (expval->num val1) (expval->num val2)))))
      (zero?-exp (exp1)
                 (let ((val1 (value-of exp1 env)))
                   (let ((num1 (expval->num val1)))
                     (if (zero? num1)
                         (bool-val #t)
                         (bool-val #f)))))

      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 env)))
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      (equal?-exp (exp1 exp2)
                  (let ([val1 (value-of exp1 env)]
                        [val2 (value-of exp2 env)])
                    (bool-val (equal? (expval->num val1) (expval->num val2)))))
      (greater?-exp (exp1 exp2)
                    (let ([val1 (value-of exp1 env)]
                          [val2 (value-of exp2 env)])
                      (bool-val (> (expval->num val1) (expval->num val2)))))
      (less?-exp (exp1 exp2)
                 (value-of (greater?-exp exp2 exp1) env))
      (let-exp (var exp1 body)
               (let ((val1 (value-of exp1 env)))
                 (value-of body
                           (extend-env var val1 env))))
      )))


;;; test
; let x = 4
; in list(x, -(x,1), -(x,3))

(define code-ast
  (let-exp 'x (const-exp 4)
    (list-exp (list (var-exp 'x)
                    (diff-exp (var-exp 'x) (const-exp 1))
                    (diff-exp (var-exp 'x) (const-exp 3))))))

(check-equal? (value-of code-ast (init-env)) (list-val (list 4 3 1)))
