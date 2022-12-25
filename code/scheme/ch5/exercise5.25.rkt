#lang eopl
(require rackunit)
(require racket/trace)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Procedure data type
(define-datatype proc proc?
  (procedure
   (vars (list-of identifier?))
   (body expression?)
   (saved-env environment?)))
; (define apply-procedure/k
;   (lambda (proc1 val cont)
;     (cases proc proc1
;       (procedure (var body saved-env)
;                  (value-of/k body
;                              (extend-env var val saved-env)
;                              cont)))))
(define apply-procedure/k
  (lambda ()
    (cases proc proc1
      (procedure (vars body saved-env)
                 (set! exp body)
                 (set! env (extend-env-vars vars val saved-env))
                 (value-of/k)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal data type
(define-datatype expval
  expval?
  (num-val (value number?))
  (bool-val (boolean boolean?))
  (proc-val (proc proc?)))

(define expval->num
  (lambda (v)
    (cases expval
      v
      (num-val (num) num)
      (else (eopl:error 'expval->num "~s" v)))))

(define expval->bool
  (lambda (v)
    (cases expval
      v
      (bool-val (bool) bool)
      (else (eopl:error 'expval->bool "~s" v)))))

(define expval->proc
  (lambda (v)
    (cases expval
      v
      (proc-val (proc) proc)
      (else (eopl:error 'expval->proc "~s" v)))))

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

(define extend-env-vars
  (lambda (vars vals env)
    (if (null? vars)
        env
        (extend-env (car vars)
                    (car vals)
                    (extend-env-vars (cdr vars) (cdr vals) env)))))

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Expression && Parsing

(define-datatype program program?
  (a-program (expr expression?)))

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
   (vars (list-of identifier?))
   (body expression?))
  (call-exp
   (rator expression?)
   (rands (list-of expression?)))
  )

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
  '((program    (expression) a-program)
    (expression (number) const-exp)
    (expression (identifier) var-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    ;todo
    (expression ("letrec" identifier "(" (separated-list identifier ",") ")" "=" expression "in" expression) letrec-exp)
    (expression ("proc" "(" (separated-list identifier ",") ")" expression) proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    ))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar-spec))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;Continuation
(define-datatype continuation continuation?
  (end-cont)
  (zero1-cont
   (saved-cont continuation?))
  (let-exp-cont
   (var identifier?)
   (body expression?)
   (saved-env environment?)
   (saved-cont continuation?))
  (if-test-cont
   (exp2 expression?)
   (exp3 expression?)
   (saved-env environment?)
   (saved-cont continuation?))
  (diff1-cont
   (exp2 expression?)
   (saved-env environment?)
   (saved-cont continuation?))
  (diff2-cont
   (val1 expval?)
   (saved-cont continuation?))
  (rator-cont
   (rands (list-of expression?))
   (saved-env environment?)
   (saved-cont continuation?))
  (rands-cont
   (val1 expval?)
   (rands (list-of expression?))
   (vals (list-of expval?))
   (saved-env environment?)
   (saved-cont continuation?)))

; (define apply-cont
;   (lambda (cont val)
;     (cases continuation cont
;       (end-cont ()
;                 (begin
;                   (eopl:printf
;                    "End of computation.~%")
;                   val))
;       (zero1-cont (saved-cont)
;                   (apply-cont saved-cont
;                               (bool-val
;                                (zero? (expval->num val)))))
;       (let-exp-cont (var body saved-env saved-cont)
;                     (value-of/k body
;                                 (extend-env var val saved-env) saved-cont))
;       (if-test-cont (exp2 exp3 saved-env saved-cont)
;                     (if (expval->bool val)
;                         (value-of/k exp2 saved-env saved-cont)
;                         (value-of/k exp3 saved-env saved-cont)))
;       (diff1-cont (exp2 saved-env saved-cont)
;                   (value-of/k exp2
;                               saved-env (diff2-cont val saved-cont)))
;       (diff2-cont (val1 saved-cont)
;                   (let ((num1 (expval->num val1))
;                         (num2 (expval->num val)))
;                     (apply-cont saved-cont
;                                 (num-val (- num1 num2)))))
;       (rator-cont (rand saved-env saved-cont)
;                   (value-of/k rand saved-env
;                               (rand-cont val saved-cont)))
;       (rand-cont (val1 saved-cont)
;                  (let ((proc (expval->proc val1)))
;                    (apply-procedure/k proc val saved-cont))))))
(define apply-cont
  (lambda ()
    (cases continuation cont
      (end-cont ()
                (eopl:printf "End of computation.~%")
                val)
      (zero1-cont (saved-cont)
                  (set! cont saved-cont)
                  (set! val (bool-val (zero? (expval->num val))))
                  (apply-cont))
      (let-exp-cont (var body saved-env saved-cont)
                    (set! cont saved-cont)
                    (set! exp body)
                    (set! env (extend-env var val saved-env))
                    (value-of/k))
      (if-test-cont (exp2 exp3 saved-env saved-cont)
                    (set! cont saved-cont)
                    (if (expval->bool val)
                        (set! exp exp2)
                        (set! exp exp3))
                    (set! env saved-env)
                    (value-of/k))
      (diff1-cont (exp2 saved-env saved-cont)
                  (set! cont (diff2-cont val saved-cont))
                  (set! exp exp2)
                  (set! env saved-env)
                  (value-of/k))
      (diff2-cont (val1 saved-cont)
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val)))
                    (set! cont saved-cont)
                    (set! val (num-val (- num1 num2)))
                    (apply-cont)))
      (rator-cont (rands saved-env saved-cont)
                  (if (null? rands)
                      (begin (set! cont saved-cont)
                             (set! proc1 (expval->proc val))
                             (set! val '())
                             (apply-procedure/k))
                      (begin (set! cont (rands-cont val (cdr rands) '() saved-env saved-cont))
                             (set! exp (car rands))
                             (set! env saved-env)
                             (value-of/k))))
      (rands-cont (rator-val rands vals saved-env saved-cont)
                  (if (null? rands)
                      (begin  (set! cont saved-cont)
                              (set! proc1 (expval->proc rator-val))
                              (set! val (reverse (cons val vals)))
                              (apply-procedure/k))
                      (begin  (set! cont (rands-cont rator-val (cdr rands) (cons val vals) saved-env saved-cont))
                              (set! exp (car rands))
                              (set! env saved-env)
                              (value-of/k)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter
(define init-env
  (lambda ()
    (extend-env 'true (bool-val #t)
                (extend-env 'false (bool-val #f)
                            (empty-env)))))
(define exp 'uninitialized)
(define env 'uninitialized)
(define cont 'uninitialized)
(define val 'uninitialized)
(define proc1 'uninitialized)

; (define value-of-program
;   (lambda (pgm)
;     (cases program pgm
;       (a-program (exp1)
;                  (value-of/k exp1 (init-env) (end-cont))))))
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (set! cont (end-cont))
                 (set! exp exp1)
                 (set! env (init-env))
                 (value-of/k)))))

; (define value-of/k
;   (lambda (exp env cont)
;     (cases expression exp
;       (const-exp (num) (apply-cont cont (num-val num)))
;       (var-exp (var) (apply-cont cont (apply-env env var)))
;       (proc-exp (var body)
;                 (apply-cont cont
;                             (proc-val
;                              (procedure var body env))))
;       (letrec-exp (p-name b-var p-body letrec-body)
;                   (value-of/k letrec-body
;                               (extend-env-rec p-name b-var p-body env)
;                               cont))
;       (zero?-exp (exp1)
;                  (value-of/k exp1 env
;                              (zero1-cont cont)))
;       (if-exp (exp1 exp2 exp3)
;               (value-of/k exp1 env
;                           (if-test-cont exp2 exp3 env cont)))
;       (let-exp (var exp1 body)
;                (value-of/k exp1 env
;                            (let-exp-cont var body env cont)))
;       (diff-exp (exp1 exp2)
;                 (value-of/k exp1 env
;                             (diff1-cont exp2 env cont)))
;       (call-exp (rator rand)
;                 (value-of/k rator env
;                             (rator-cont rand env cont))))))

(define value-of/k
  (lambda ()
    (cases expression exp
      (const-exp (num)
                 (set! val (num-val num))
                 (apply-cont))
      (var-exp (var)
               (set! val (apply-env env var))
               (apply-cont))
      (proc-exp (vars body)
                (set! val (proc-val (procedure vars body env)))
                (apply-cont))
      (letrec-exp (p-name b-vars p-body letrec-body)
                  (set! exp letrec-body)
                  (set! env (extend-env-rec p-name b-vars p-body env))
                  (value-of/k))
      (zero?-exp (exp1)
                 (set! cont (zero1-cont cont))
                 (set! exp exp1)
                 (value-of/k))
      (let-exp (var exp1 body)
               (set! cont (let-exp-cont var body env cont))
               (set! exp exp1)
               (value-of/k))
      (if-exp (exp1 exp2 exp3)
              (set! cont (if-test-cont exp2 exp3 env cont))
              (set! exp exp1)
              (value-of/k))
      (diff-exp (exp1 exp2)
                (set! cont (diff1-cont exp2 env cont))
                (set! exp exp1)
                (value-of/k))
      (call-exp (rator rand)
                (set! cont (rator-cont rand env cont))
                (set! exp rator)
                (value-of/k)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; run
(define run
  (lambda (code)
    (value-of-program (scan&parse code))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; (trace value-of/k)
;;; test
(define code1
  "
  letrec double(x) = if zero?(x) then 0 else -((double -(x,1)), -2)
  in (double 6)
   ")
(check-equal? (run code1) (num-val 12))

(define code2
  "
  letrec id(x) = x
  in (id 0)
   ")
(check-equal? (run code2) (num-val 0))

(define code3
  "
  let lt2? = proc(x) if zero?(x) then true else if zero?(-(x, 1)) then true else false
  in let sum = proc(x) proc(y) -(x, -(0, y))
     in letrec fib(x) = if (lt2? x) then x else ((sum (fib -(x, 1))) (fib -(x, 2)))
        in (fib 15)
   ")
(check-equal? (run code3) (num-val 610))


(define code4
  "
  let a = 114
  in let b = 514
     in let c = 114514
        in let sum = proc(x, y, z) -(x, -(0, -(y, -(0, z))))
           in (sum a b c)
  ")
(check-equal? (run code4) (num-val 115142))

(define code5
      "
      let foo = proc() 114514
      in (foo)
      ")
(check-equal? (run code5) (num-val 114514))