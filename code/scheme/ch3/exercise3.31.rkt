#lang eopl
(require rackunit)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Procedure data type
; procedure : Var × Exp × Env → Proc
(define-datatype proc proc?
  (procedure
   (vars (list-of identifier?))
   (body expression?)
   (saved-env environment?)))
; apply-procedure : Proc × ExpVal → ExpVal
(define apply-procedure
  (lambda (proc1 vals)
    (cases proc proc1
      (procedure (vars body saved-env)
                 (value-of body (extend-env-list vars vals saved-env))))))

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
(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var identifier?)
   (val expval?)
   (env environment?))
  (extend-env-rec
   (p-name identifier?)
   (b-vars (list-of identifier?))
   (body expression?)
   (env environment?)))

(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
                 (eopl:error 'apply-env))
      (extend-env (saved-var saved-val saved-env)
                  (if (eqv? saved-var search-var)
                      saved-val
                      (apply-env saved-env search-var)))
      (extend-env-rec (p-name b-vars p-body saved-env)
                      (if (eqv? search-var p-name)
                          (proc-val (procedure b-vars p-body env))
                          (apply-env saved-env search-var))))))

(define extend-env-list
  (lambda (vars vals env)
    (if (null? vars)
        env
        (extend-env (car vars)
                    (car vals)
                    (extend-env-list (cdr vars) (cdr vals) env)))))

; (define extend-env-rec
;   (lambda (p-name b-var body saved-env)
;     (let ((vec (make-vector 1)))
;       (let ((new-env (extend-env p-name vec saved-env)))
;         (vector-set! vec 0
;                      (proc-val (procedure b-var body new-env)))
;         new-env))))

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
   (p-name identifier?)
   (b-vars (list-of identifier?))
   (p-body expression?)
   (letrec-body expression?))
  (proc-exp
   (var identifier?)
   (body expression?))
  (call-exp
   (rator expression?)
   (rand (list-of expression?)))
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
      (letrec-exp (proc-name bound-vars proc-body letrec-body)
                  (value-of letrec-body (extend-env-rec proc-name bound-vars proc-body env)))
      (proc-exp (var body)
                (proc-val (procedure var body env)))
      (call-exp (rator rands)
                ; (write env)
                ; (newline)
                (let ((proc (expval->proc (value-of rator env)))
                      (args (map (lambda (rand) (value-of rand env)) rands)))
                  (apply-procedure proc args)))
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
    (expression ("letrec" identifier "(" (arbno identifier) ")" "=" expression "in" expression) letrec-exp)
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    (expression ("(" expression (arbno expression ) ")") call-exp)
    ))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar-spec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define init-env
  (lambda ()
    (empty-env)))

;;; run
(define run
  (lambda (code)
    (value-of (scan&parse code) (init-env))))

;;; test
(define code1
  "
  letrec add(x y)
          = if zero?(x) then y else -((add -(x, 1) y), -1)
  in (add 7 6)
   ")
(check-equal? (run code1) (num-val 13))

(define code2
  "
  letrec sum(x y z)
          = -(x, -(0, -(y, -(0, z))))
  in (sum 3 4 5)
   ")
(check-equal? (run code2) (num-val 12))
