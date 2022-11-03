#lang eopl
(require rackunit)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Procedure data type
; procedure : Var × Exp × Env → Proc
(define-datatype proc proc?
  (procedure
   (var identifier?)
   (body expression?)
   (saved-env environment?)))
; apply-procedure : Proc × ExpVal → ExpVal
(define apply-procedure
  (lambda (proc1 val)
    (cases proc proc1
      (procedure (var body saved-env)
                 (value-of body (extend-env var val saved-env))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal data type
(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val (proc proc?))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal -> scheme value

(define expval->num
  (lambda (v)
    (cases expval v
      	(num-val (num) num)
      	(else (eopl:error)))))

(define expval->bool
  (lambda (v)
    (cases expval v
      	(bool-val (bool) bool)
      	(else (eopl:error)))))

(define expval->proc
  (lambda (v)
    (cases expval v
      	(proc-val (proc) proc)
      	(else (eopl:error)))))

(define expval->scheme-val
  (lambda (v)
    (cases expval v
      (num-val (num) num)
      (bool-val (bool) bool)
      (proc-val (proc) proc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Env
(define empty-env
  (lambda ()
    (list 'env)))

(define extend-env
  (lambda (var val saved-env)
    (list 'env var val saved-env)))

(define extend-env-rec
  (lambda (p-names b-vars bodys saved-env)
    (letrec ((make-new-env (lambda (names)
                             (if (null? names)
                                 saved-env
                                 (extend-env (car names) (make-vector 1) (make-new-env (cdr names)))))))
      (let ((new-env (make-new-env p-names)))
        (letrec ((set!-new-env (lambda (vars bodys env)
                                 (if (null? vars)
                                     new-env
                                     (let ((vec (env-val env)))
                                       (begin
                                         (vector-set! vec 0 (proc-val (procedure (car vars) (car bodys) new-env)))
                                         (set!-new-env (cdr vars) (cdr bodys) (env-saved env))))))))
          (set!-new-env b-vars bodys new-env))))))

(define apply-env
  (lambda (env search-var)
    (cond [(empty-env? env) (eopl:error 'apply-env (symbol->string search-var))]
          [(eqv? (env-var env) search-var)
           (if (vector? (env-val env))
               (vector-ref (env-val env) 0)
               (env-val env))]
          [else (apply-env (env-saved env) search-var)])))

(define env-var
  (lambda (env)
    (cadr env)))

(define env-val
  (lambda (env)
    (caddr env)))

(define env-saved
  (lambda (env)
    (cadddr env)))

(define empty-env?
  (lambda (env)
    (equal? env (empty-env))))

(define environment?
  (lambda (env)
    (eqv? (car env) 'env)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Expression data type
(define identifier?
  (lambda (exp)
    (and (symbol? exp)
         (not (eqv? exp 'lambda)))))

(define-datatype expression expression?
  (const-exp
   (num number?))
  (if-exp
   (exp1 expression?)
   (exp2 expression?)
   (exp3 expression?))
  (zero?-exp
   (exp1 expression?))
  (var-exp
   (var identifier?))
  (diff-exp
   (exp1 expression?)
   (exp2 expression?))
  (let-exp
   (var  identifier?)
   (exp  expression?)
   (body expression?))
  (letrec-exp
   (p-names (list-of identifier?))
   (b-vars (list-of identifier?))
   (p-body (list-of expression?))
   (letrec-body expression?))
  (proc-exp
   (var identifier?)
   (body expression?))
  (call-exp
   (rator expression?)
   (rand expression?))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter

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
      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 env)))
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      (zero?-exp (exp1)
                 (let ((val1 (value-of exp1 env)))
                   (let ((num1 (expval->num val1)))
                     (if (zero? num1)
                         (bool-val #t)
                         (bool-val #f)))))
      (let-exp (var exp body)
               (value-of body
                         (extend-env var (value-of exp env) env)))
      (letrec-exp (proc-names bound-vars proc-bodys letrec-body)
                  (value-of letrec-body
                            (extend-env-rec proc-names bound-vars proc-bodys env)))
      (proc-exp (var body)
                (proc-val (procedure var body env)))
      (call-exp (rator rand)
                (let ((proc (expval->proc (value-of rator env)))
                      (arg (value-of rand env)))
                  (apply-procedure proc arg)))
      )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; parse
(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)
    ))

(define the-grammar-spec
  '(
    (expression (number) const-exp)
    (expression (identifier) var-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("letrec" (arbno identifier "(" identifier ")" "=" expression)"in" expression) letrec-exp)
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    (expression ("(" expression expression ")") call-exp)
    ))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar-spec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define init-env
  (lambda ()
    (extend-env 'true (bool-val #t)
                (extend-env 'false (bool-val #f)
                            (empty-env)))))


;;; run
(define run
  (lambda (code)
    (value-of (scan&parse code) (init-env))))

;;; test
(define code1
  "
  letrec
    even(x) = if zero?(x) then true else (odd -(x,1))
    odd(x) = if zero?(x) then false else (even -(x,1))
  in (odd 14)
")
(check-equal? (run code1) (bool-val #f))

(define code2
  "
  letrec
    even(x) = if zero?(x) then true else (odd -(x,1))
    odd(x) = if zero?(x) then false else (even -(x,1))
  in (odd 15)
")
(check-equal? (run code2) (bool-val #t))

(define code3
  "
  letrec
    even(x) = if zero?(x) then true else (odd -(x,1))
    odd(x) = if zero?(x) then false else (even -(x,1))
  in (odd 114514)
")
(check-equal? (run code3) (bool-val #f))

(define code4
  "
  letrec
    even(x) = if zero?(x) then true else (odd -(x,1))
    odd(x) = if zero?(x) then false else (even -(x,1))
  in (even 114514)
")
(check-equal? (run code4) (bool-val #t))