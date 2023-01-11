#lang eopl
(require rackunit)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Procedure data type
(define-datatype proc
                 proc?
                 (procedure (vars (list-of identifier?))
                            (body expression?)
                            (saved-env environment?)))

(define apply-procedure
  (lambda (proc1 vals)
    (cases proc
           proc1
           (procedure (vars body saved-env)
                      (value-of body (extend-env-list vars vals saved-env))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal data type
(define-datatype expval
                 expval?
                 (num-val (value number?))
                 (bool-val (boolean boolean?))
                 (proc-val (proc proc?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal -> scheme value
(define expval->num
  (lambda (v) (cases expval v (num-val (num) num) (else (eopl:error)))))

(define expval->bool
  (lambda (v) (cases expval v (bool-val (bool) bool) (else (eopl:error)))))

(define expval->proc
  (lambda (v) (cases expval v (proc-val (proc) proc) (else (eopl:error)))))

(define expval->scheme-val
  (lambda (v)
    (cases expval
           v
           (num-val (num) num)
           (bool-val (bool) bool)
           (proc-val (proc) proc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Env
(define-datatype environment
                 environment?
                 (empty-env)
                 (extend-env (var identifier?) (val expval?) (env environment?))
                 (extend-env-rec-list (p-names (list-of identifier?))
                                      (b-varss (list-of (list-of identifier?)))
                                      (bodies (list-of expression?))
                                      (env environment?)))

(define apply-env
  (lambda (env search-var)
    (cases
     environment
     env
     (empty-env () (eopl:error 'apply-env "~s" search-var))
     (extend-env (saved-var saved-val saved-env)
                 (if (eqv? saved-var search-var)
                     saved-val
                     (apply-env saved-env search-var)))
     (extend-env-rec-list
      (p-names b-varss p-bodies saved-env)
      (let search ([p-names p-names] [b-varss b-varss] [p-bodies p-bodies])
        (if (null? p-names)
            (apply-env saved-env search-var)
            (if (eqv? (car p-names) search-var)
                (proc-val (procedure (car b-varss) (car p-bodies) env))
                (search (cdr p-names) (cdr b-varss) (cdr p-bodies)))))))))

(define extend-env-list
  (lambda (vars vals env)
    (if (null? vars)
        env
        (extend-env (car vars)
                    (car vals)
                    (extend-env-list (cdr vars) (cdr vals) env)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Expression data type
(define identifier? (lambda (exp) (and (symbol? exp) (not (eqv? exp 'lambda)))))

(define cps-in-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define cps-in-grammar-spec
  '((expression (number) const-exp)
    (expression (identifier) var-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("+" "(" (separated-list expression ",") ")") sum-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression
     ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" expression)
               "in"
               expression)
     letrec-exp)
    (expression ("proc" "(" (arbno identifier) ")" expression) proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)))

(define scan&parse
  (sllgen:make-string-parser cps-in-lexical-spec cps-in-grammar-spec))

(sllgen:make-define-datatypes cps-in-lexical-spec cps-in-grammar-spec)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter
; value-of : Exp × Env → ExpVal
(define value-of
  (lambda (exp env)
    (cases
     expression
     exp
     (const-exp (num) (num-val num))
     (var-exp (var) (apply-env env var))
     (diff-exp (exp1 exp2)
               (let ([val1 (value-of exp1 env)] [val2 (value-of exp2 env)])
                 (let ([num1 (expval->num val1)] [num2 (expval->num val2)])
                   (num-val (- num1 num2)))))
     (sum-exp
      (exps)
      (let ([vals (map (lambda (exp1) (expval->num (value-of exp1 env))) exps)])
        (let loop ([vals vals] [res 0])
          (if (null? vals)
              (num-val res)
              (loop (cdr vals) (+ res (car vals)))))))
     (if-exp
      (exp1 exp2 exp3)
      (let ([val1 (value-of exp1 env)])
        (if (expval->bool val1) (value-of exp2 env) (value-of exp3 env))))
     (zero?-exp (exp1)
                (let ([val1 (value-of exp1 env)])
                  (let ([num1 (expval->num val1)])
                    (if (zero? num1) (bool-val #t) (bool-val #f)))))
     (let-exp (var exp body)
              (value-of body (extend-env var (value-of exp env) env)))
     (letrec-exp
      (proc-names bound-varss proc-bodies letrec-body)
      (value-of letrec-body
                (extend-env-rec-list proc-names bound-varss proc-bodies env)))
     (proc-exp (vars body) (proc-val (procedure vars body env)))
     (call-exp (rator rands)
               (let ([proc (expval->proc (value-of rator env))]
                     [args (map (lambda (rand) (value-of rand env)) rands)])
                 (apply-procedure proc args))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define init-env
  (lambda ()
    (extend-env 'true
                (bool-val #t)
                (extend-env 'false (bool-val #f) (empty-env)))))

;;; run
(define run (lambda (code) (value-of (scan&parse code) (init-env))))

;;; test
(define str0
  "let sum = proc(x y z) -(x, -(0, -(y, -(0, z))))
   in (sum 11 45 14)")
(check-equal? (run str0) (num-val 70))

(define str1 "let foo = proc() 114514
   in (foo)")
(check-equal? (run str1) (num-val 114514))

(define str2
  "letrec equal?(x n) = if zero?(x)
                             then zero?(n)
                             else (equal? -(x, 1) -(n, 1))
   in let f = proc(x) x
      in let g = proc(x y) +(x, y, 37)
         in let h = proc(x y z) +(x, y, z, 17)
            in let y = 73
               in let p = proc(x) if zero?(x)
                                  then 17
                                  else if (equal? x 1)
                                       then (f -(x, 13))
                                       else if (equal? x 2)
                                            then +(22, -(x, 3), x)
                                            else if (equal? x 3)
                                                 then +(22, (f x), 37)
                                                 else if (equal? x 4)
                                                      then (g 22 (f x))
                                                      else if (equal? x 5)
                                                           then +(22, (f x), 33, (g y 37))
                                                           else (h (f x) -(44, y) (g y 37))
                   in +((p 1), (p 2), (p 3), (p 4), (p 5), (p 73))")

(define res-str2
  (let ([f (lambda (x) x)]
        [g (lambda (x y) (+ x y 37))]
        [h (lambda (x y z) (+ x y z 17))]
        [y 73])
    (let ([p (lambda (x)
               (cond
                 [(zero? x) 17]
                 [(= x 1) (f (- x 13))]
                 [(= x 2) (+ 22 (- x 3) x)]
                 [(= x 3) (+ 22 (f x) 37)]
                 [(= x 4) (g 22 (f x))]
                 [(= x 5) (+ 22 (f x) 33 (g y 37))]
                 [else (h (f x) (- 44 y) (g y 37))]))])
      (+ (p 1) (p 2) (p 3) (p 4) (p 5) (p 73)))))

(check-equal? (run str2) (num-val res-str2))
