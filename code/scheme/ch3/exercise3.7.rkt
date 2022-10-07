#lang eopl
(require "let-interpreter.rkt")
(require rackunit)

(define-datatype expression expression?
  (const-exp
   (num number?))
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

      (let-exp (var exp1 body)
               (let ((val1 (value-of exp1 env)))
                 (value-of body
                           (extend-env var val1 env))))
      )))


(define code-ast1
  (add-exp (const-exp 14) (diff-exp (minus-exp (const-exp 5)) (const-exp 9))))
(check-equal? (value-of code-ast1 (init-env)) (num-val 0))


(define code-ast2
  (mul-exp (const-exp 14) (add-exp (var-exp 'x) (const-exp 6))))
(check-equal? (value-of code-ast2 (init-env)) (num-val 224))

(define code-ast3
  (quotient-exp (var-exp 'v) (const-exp 2)))
(check-equal? (value-of code-ast3 (init-env)) (num-val 2))

