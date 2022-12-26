#lang eopl
(require rackunit)
(require racket/trace)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Procedure data type
(define-datatype proc proc?
  (procedure
   (var identifier?)
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
    (cases proc reg1
      (procedure (var body saved-env)
                 (set! reg1 body)
                 (set! reg2 (extend-env var reg2 saved-env))
                 (set! reg3 reg3)
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
   (b-var identifier?)
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
      (extend-env-rec (p-name b-var p-body saved-env)
                      (if (eqv? search-var p-name)
                          (proc-val (procedure b-var p-body env))
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
   (b-var identifier?)
   (p-body expression?)
   (letrec-body expression?))
  (proc-exp
   (var identifier?)
   (body expression?))
  (call-exp
   (rator expression?)
   (rand expression?))
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
    (expression ("letrec" identifier "(" identifier ")" "=" expression "in" expression) letrec-exp)
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    (expression ("(" expression expression ")") call-exp)
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
   (rand expression?)
   (saved-env environment?)
   (saved-cont continuation?))
  (rand-cont
   (val1 expval?)
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
    (cases continuation reg1
      (end-cont ()
                (eopl:printf "End of computation.~%")
                reg2)
      (zero1-cont (saved-cont)
                  (set! reg1 saved-cont)
                  (set! reg2 (bool-val (zero? (expval->num reg2))))
                  (apply-cont))
      (let-exp-cont (var body saved-env saved-cont)
                    (set! reg3 saved-cont)
                    (set! reg1 body)
                    (set! reg2 (extend-env var reg2 saved-env))
                    (value-of/k))
      (if-test-cont (exp2 exp3 saved-env saved-cont)
                    (set! reg3 saved-cont)
                    (if (expval->bool reg2)
                        (set! reg1 exp2)
                        (set! reg1 exp3))
                    (set! reg2 saved-env)
                    (value-of/k))
      (diff1-cont (exp2 saved-env saved-cont)
                  (set! reg3 (diff2-cont reg2 saved-cont))
                  (set! reg1 exp2)
                  (set! reg2 saved-env)
                  (value-of/k))
      (diff2-cont (val1 saved-cont)
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num reg2)))
                    (set! reg1 saved-cont)
                    (set! reg2 (num-val (- num1 num2)))
                    (apply-cont)))
      (rator-cont (rand saved-env saved-cont)
                  (set! reg3 (rand-cont reg2 saved-cont))
                  (set! reg1 rand)
                  (set! reg2 saved-env)
                  (value-of/k))
      (rand-cont (rator-val saved-cont)
                 (let ((rator-proc (expval->proc rator-val)))
                   (set! reg3 saved-cont)
                   (set! reg1 rator-proc)
                   (set! reg2 reg2)
                   (apply-procedure/k))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter
(define init-env
  (lambda ()
    (extend-env 'true (bool-val #t)
                (extend-env 'false (bool-val #f)
                            (empty-env)))))

; (value-of/k exp env cont)
; (apply-cont cont val)
; (apply-procedure/k proc1 val cont)
(define reg1 'uninitialized)
(define reg2 'uninitialized)
(define reg3 'uninitialized)

; (define value-of-program
;   (lambda (pgm)
;     (cases program pgm
;       (a-program (exp1)
;                  (value-of/k exp1 (init-env) (end-cont))))))
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (set! reg1 exp1)
                 (set! reg2 (init-env))
                 (set! reg3 (end-cont))
                 (value-of/k)))))


(define value-of/k
  (lambda ()
    (cases expression reg1
      (const-exp (num)
                 (set! reg2 (num-val num))
                 (set! reg1 reg3)
                 (apply-cont))
      (var-exp (var)
               (set! reg2 (apply-env reg2 var))
               (set! reg1 reg3)
               (apply-cont))
      (proc-exp (var body)
                (set! reg2 (proc-val (procedure var body reg2)))
                (set! reg1 reg3)
                (apply-cont))
      (letrec-exp (p-name b-var p-body letrec-body)
                  (set! reg1 letrec-body)
                  (set! reg2 (extend-env-rec p-name b-var p-body reg2))
                  (set! reg3 reg3)
                  (value-of/k))
      (zero?-exp (exp1)
                 (set! reg3 (zero1-cont reg3))
                 (set! reg1 exp1)
                 (set! reg2 reg2)
                 (value-of/k))
      (let-exp (var exp1 body)
               (set! reg3 (let-exp-cont var body reg2 reg3))
               (set! reg1 exp1)
               (set! reg2 reg2)
               (value-of/k))
      (if-exp (exp1 exp2 exp3)
              (set! reg3 (if-test-cont exp2 exp3 reg2 reg3))
              (set! reg1 exp1)
              (set! reg2 reg2)
              (value-of/k))
      (diff-exp (exp1 exp2)
                (set! reg3 (diff1-cont exp2 reg2 reg3))
                (set! reg1 exp1)
                (set! reg2 reg2)
                (value-of/k))
      (call-exp (rator rand)
                (set! reg3 (rator-cont rand reg2 reg3))
                (set! reg1 rator)
                (set! reg2 reg2)
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

;;; one register for one parameter