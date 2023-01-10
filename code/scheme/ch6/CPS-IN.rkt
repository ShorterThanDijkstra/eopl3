#lang eopl

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Procedure data type
(define-datatype proc
                 proc?
                 (procedure (vars (list-of identifier?))
                            (body TfExp?)
                            (saved-env environment?)))

; apply-procedure : Proc × ExpVal → ExpVal
(define apply-procedure/k
  (lambda (proc1 args cont)
    (cases proc
           proc1
           (procedure
            (vars body saved-env)
            (value-of/k body (extend-env* vars args saved-env) cont)))))

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
(define-datatype environment
                 environment?
                 (empty-env)
                 (extend-env (var identifier?) (val expval?) (env environment?))
                 (extend-env-rec** (p-names (list-of identifier?))
                                   (b-varss (list-of (list-of identifier?)))
                                   (bodies (list-of TfExp?))
                                   (env environment?)))

(define apply-env
  (lambda (env search-var)
    (cases
     environment
     env
     (empty-env () (eopl:error 'apply-env))
     (extend-env (saved-var saved-val saved-env)
                 (if (eqv? saved-var search-var)
                     saved-val
                     (apply-env saved-env search-var)))
     (extend-env-rec**
      (p-names b-varss p-bodies saved-env)
      (let search ([p-names p-names] [b-varss b-varss] [p-bodies p-bodies])
        (if (null? p-names)
            (apply-env saved-env search-var)
            (if (eqv? (car p-names) search-var)
                (proc-val (procedure (car b-varss) (car p-bodies) env))
                (search (cdr p-names) (cdr b-varss) (cdr p-bodies)))))))))

(define extend-env*
  (lambda (vars vals env)
    (if (null? vars)
        env
        (extend-env (car vars)
                    (car vals)
                    (extend-env* (cdr vars) (cdr vals) env)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Expression && Parsing
(define identifier? (lambda (exp) (and (symbol? exp) (not (eqv? exp 'lambda)))))

(define cps-out-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define cps-out-grammar-spec
  '((CpsProgram (TfExp) a-cps-program)
    (SimpleExp (number) cps-const-exp)
    (SimpleExp (identifier) cps-var-exp)
    (SimpleExp ("-" "(" SimpleExp "," SimpleExp ")") cps-diff-exp)
    (SimpleExp ("zero?" "(" SimpleExp ")") cps-zero?-exp)
    (SimpleExp ("proc" "(" (arbno identifier) ")" TfExp) cps-proc-exp)
    (TfExp (SimpleExp) simple-exp->exp)
    (TfExp ("let" identifier "=" SimpleExp "in" TfExp) cps-let-exp)
    (TfExp ("letrec"
            (arbno identifier "(" (separated-list identifier ",") ")" "=" TfExp)
            "in"
            TfExp)
           cps-letrec-exp)
    (TfExp ("if" SimpleExp "then" TfExp "else" TfExp) cps-if-exp)
    (TfExp ("(" SimpleExp (arbno SimpleExp) ")") cps-call-exp)))

(define list-cps-out-datatypes
  (lambda ()
    (sllgen:list-define-datatypes cps-out-lexical-spec cps-out-grammar-spec)))

(define scan&parse
  (sllgen:make-string-parser cps-out-lexical-spec cps-out-grammar-spec))

(sllgen:make-define-datatypes cps-out-lexical-spec cps-out-grammar-spec)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Continuation

(define-datatype continuation continuation? (end-cont))

(define apply-cont
  (lambda (cont val) (cases continuation cont (end-cont () val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter
(define value-of-simple-exp
  (lambda (simple env)
    (cases
     SimpleExp
     simple
     (cps-const-exp (num) (num-val num))
     (cps-var-exp (var) (apply-env env var))
     (cps-diff-exp (exp1 exp2)
                   (let ([val1 (value-of-simple-exp exp1 env)]
                         [val2 (value-of-simple-exp exp2 env)])
                     (let ([num1 (expval->num val1)] [num2 (expval->num val2)])
                       (num-val (- num1 num2)))))
     (cps-zero?-exp (exp1)
                    (let ([val1 (value-of-simple-exp exp1 env)])
                      (let ([num1 (expval->num val1)])
                        (if (zero? num1) (bool-val #t) (bool-val #f)))))
     (cps-proc-exp (vars body) (proc-val (procedure vars body env))))))

; value-of/k : TfExp × Env × Cont → FinalAnswer
(define value-of/k
  (lambda (exp env cont)
    (cases
     TfExp
     exp
     (simple-exp->exp (simple)
                      (apply-cont cont (value-of-simple-exp simple env)))
     (cps-let-exp
      (var rhs body)
      (let ([val (value-of-simple-exp rhs env)])
        (value-of/k body (extend-env (list var) (list val) env) cont)))
     (cps-letrec-exp (p-names b-varss p-bodies letrec-body)
                     (value-of/k letrec-body
                                 (extend-env-rec** p-names b-varss p-bodies env)
                                 cont))
     (cps-if-exp (simple1 body1 body2)
                 (if (expval->bool (value-of-simple-exp simple1 env))
                     (value-of/k body1 env cont)
                     (value-of/k body2 env cont)))
     (cps-call-exp
      (rator rands)
      (let ([rator-proc (expval->proc (value-of-simple-exp rator env))]
            [rand-vals
             (map (lambda (simple) (value-of-simple-exp simple env)) rands)])
        (apply-procedure/k rator-proc rand-vals cont))))))

(define init-env
  (lambda ()
    (extend-env 'true
                (bool-val #t)
                (extend-env 'false (bool-val #f) (empty-env)))))

(define value-of-program
  (lambda (pgm)
    (cases CpsProgram
           pgm
           (a-cps-program (exp1) (value-of/k exp1 (init-env) (end-cont))))))

(define run (lambda (code) (value-of-program (scan&parse code))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; CPS-IN
(define cps-in-lexical-spec
  '([whitespace (whitespace) skip]
    [comment ("%" (arbno (not #\newline))) skip]
    [identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol]
    [number (digit (arbno digit)) number]
    [number ("-" digit (arbno digit)) number]))

(define cps-in-grammar
  '([program (expression) a-program]
    [expression (number) const-exp]
    [expression ("-" "(" expression "," expression ")") diff-exp]
    [expression ("zero?" "(" expression ")") zero?-exp]
    [expression ("if" expression "then" expression "else" expression) if-exp]
    [expression
     ("letrec"
      (arbno identifier "(" (separated-list identifier ",") ")" "=" expression)
      "in"
      expression)
     letrec-exp]
    [expression (identifier) var-exp]
    [expression ("let" identifier "=" expression "in" expression) let-exp]
    [expression
     ("proc" "(" (separated-list identifier ",") ")" expression)
     proc-exp]
    [expression ("(" expression (arbno expression) ")") call-exp]))

(sllgen:make-define-datatypes cps-in-lexical-spec cps-in-grammar)

(define scan&parse-cps-in
  (sllgen:make-string-parser cps-in-lexical-spec cps-in-grammar))

; translate-of-pragram : Pragram -> CpsProgram
(define translate-of-pragram
  (lambda (pgm)
    (cases program pgm (a-program (exp1) (a-cps-program (translate-of exp1))))))

;translate-of-simple-exp : Exp -> SimpleExp
(define translate-of-simple-exp
  (lambda (exp1)
    (cases expression
           exp1
           (const-exp (num) (cps-const-exp num))
           (var-exp (var) (cps-var-exp var))
           (diff-exp (exp1 exp2)
                     (let ([simple-exp1 (translate-of-simple-exp exp1)]
                           [simple-exp2 (translate-of-simple-exp exp2)])
                       (cps-diff-exp simple-exp1 simple-exp2)))
           (zero?-exp (exp1)
                      (let ([simple-exp1 (translate-of-simple-exp exp1)])
                        (cps-zero?-exp simple-exp1)))
           (proc-exp (vars body) (cps-proc-exp vars body))
           (else (eopl:error 'translate-of-simple-exp)))))

; translate : Exp -> TfExp
(define translate-of
  (lambda (exp1)
    (cases
     expression
     exp1
     (const-exp (num) (simple-exp->exp (cps-const-exp num)))
     (var-exp (var) (simple-exp->exp (cps-var-exp var)))
     (diff-exp (exp1 exp2)
               (let ([simple-exp1 (translate-of-simple-exp exp1)]
                     [simple-exp2 (translate-of-simple-exp exp2)])
                 (simple-exp->exp (cps-diff-exp simple-exp1 simple-exp2))))
     (if-exp (exp1 exp2 exp3)
             (let ([simple-exp1 (translate-of-simple-exp exp1)]
                   [tf-exp2 (translate-of exp2)]
                   [tf-exp3 (translate-of exp3)])
               (cps-if-exp simple-exp1 tf-exp2 tf-exp3)))
     (zero?-exp (exp1)
                (let ([simple-exp1 (translate-of-simple-exp exp1)])
                  (simple-exp->exp (cps-zero?-exp simple-exp1))))
     (proc-exp (vars body)
               (simple-exp->exp (cps-proc-exp vars (translate-of body))))
     (let-exp (var exp1 body)
              (let ([simple-exp1 (translate-of-simple-exp exp1)]
                    [tf-body (translate-of body)])
                (cps-let-exp var simple-exp1 tf-body)))
     (letrec-exp
      (proc-names bound-varss proc-bodies letrec-body)
      (let ([tf-proc-bodies
             (map (lambda (exp1) (translate-of exp1)) proc-bodies)]
            [tf-letrec-body (translate-of letrec-body)])
        (cps-letrec-exp proc-names bound-varss tf-proc-bodies tf-letrec-body)))
     (call-exp
      (rator rands)
      (let ([simple-rator (translate-of-simple-exp rator)]
            [simple-rands
             (map (lambda (exp1) (translate-of-simple-exp exp1)) rands)])
        (cps-call-exp simple-rator simple-rands))))))