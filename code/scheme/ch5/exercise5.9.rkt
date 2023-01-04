#lang eopl
(require rackunit)
(require racket/trace)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Procedure data type
; procedure : Var × Exp × Env → Proc
(define-datatype
 proc
 proc?
 (procedure (var identifier?) (body expression?) (saved-env environment?)))
; apply-procedure : Proc × ExpVal → ExpVal
; apply-procedure/k : Proc × ExpVal × Cont → FinalAnswer
(define apply-procedure/k
  (lambda (proc1 val cont)
    (cases proc
           proc1
           (procedure
            (var body saved-env)
            (value-of/k body (extend-env var (newref val) saved-env) cont)))))

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
; Store
; empty-store : () → Sto
(define empty-store (lambda () '()))
; usage: A Scheme variable containing the current state
; of the store. Initially set to a dummy value.

(define the-store 'uninitialized)

; get-store : () → Sto
(define get-store (lambda () the-store))

; initialize-store! : () → Unspecified
; usage: (initialize-store!) sets the-store to the empty store
(define initialize-store! (lambda () (set! the-store (empty-store))))

; reference? : SchemeVal → Bool
(define reference? (lambda (v) (integer? v)))

; newref : ExpVal → Ref
(define newref
  (lambda (val)
    (let ([next-ref (length the-store)])
      (set! the-store (append the-store (list val)))
      next-ref)))

; deref : Ref → ExpVal
(define deref (lambda (ref) (list-ref the-store ref)))

; setref! : Ref × ExpVal → Unspecified
; usage: sets the-store to a state like the original, but with
; position ref containing val.
(define setref!
  (lambda (ref val)
    (set!
     the-store
     (letrec ([setref-inner
               ; usage: returns a list like store1, except that
               ; position ref1 contains val.
               (lambda (store1 ref1)
                 (cond
                   [(null? store1)
                    (eopl:error "report-invalid-reference ~s" ref the-store)]
                   [(zero? ref1) (cons val (cdr store1))]
                   [else
                    (cons (car store1)
                          (setref-inner (cdr store1) (- ref1 1)))]))])
       (setref-inner the-store ref)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Env

(define-datatype
 environment
 environment?
 (empty-env)
 (extend-env (var identifier?) (ref reference?) (env environment?))
 (extend-env-rec (p-name identifier?)
                 (b-var identifier?)
                 (body expression?)
                 (env environment?)))

(define apply-env
  (lambda (env search-var)
    (cases environment
           env
           (empty-env () (eopl:error 'apply-env "No binding for ~s" search-var))
           (extend-env
            (bvar ref saved-env)
            (if (eqv? search-var bvar) ref (apply-env saved-env search-var)))
           (extend-env-rec (p-name b-var p-body saved-env)
                           (if (eqv? search-var p-name)
                               (newref (proc-val (procedure b-var p-body env)))
                               (apply-env saved-env search-var))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Expression && Parsing

(define-datatype program program? (a-program (expr expression?)))

(define identifier? (lambda (exp) (and (symbol? exp) (not (eqv? exp 'lambda)))))

(define-datatype
 expression
 expression?
 (const-exp (num number?))
 (if-exp (exp1 expression?) (exp2 expression?) (exp3 expression?))
 (zero?-exp (exp1 expression?))
 (var-exp (var identifier?))
 (assign-exp (var identifier?) (exp1 expression?))
 (diff-exp (exp1 expression?) (exp2 expression?))
 (let-exp (var identifier?) (exp expression?) (body expression?))
 (letrec-exp (p-name identifier?)
             (b-var identifier?)
             (p-body expression?)
             (letrec-body expression?))
 (proc-exp (var identifier?) (body expression?))
 (call-exp (rator expression?) (rand expression?))
 (seq-exp (fst expression?) (exps (list-of expression?))))

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define the-grammar-spec
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression (identifier) var-exp)
    (expression ("set" identifier "=" expression) assign-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression
     ("letrec" identifier "(" identifier ")" "=" expression "in" expression)
     letrec-exp)
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    (expression ("(" expression expression ")") call-exp)
    (expression ("{" expression ";" (separated-list expression ";") "}")
                seq-exp)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar-spec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;Continuation
(define-datatype
 continuation
 continuation?
 (end-cont)
 (zero1-cont (cont continuation?))
 (let-exp-cont (var identifier?)
               (body expression?)
               (env environment?)
               (saved-cont continuation?))
 (if-test-cont (exp2 expression?)
               (exp3 expression?)
               (env environment?)
               (saved-cont continuation?))
 (diff1-cont (exp2 expression?) (env environment?) (saved-cont continuation?))
 (diff2-cont (val1 expval?) (saved-cont continuation?))
 (rator-cont (rand expression?) (env environment?) (saved-cont continuation?))
 (rand-cont (val1 expval?) (saved-cont continuation?))
 (set-rhs-cont (var identifier?) (env environment?) (saved-cont continuation?))
 (seq-cont (exps (list-of expression?))
           (env environment?)
           (saved-cont continuation?)))

; apply-cont : Cont × ExpVal → FinalAnswer
(define apply-cont
  (lambda (cont val)
    (cases
     continuation
     cont
     (end-cont ()
               (begin
                 (eopl:printf "End of computation:~s.~%" val)
                 val))
     (zero1-cont (saved-cont)
                 (apply-cont saved-cont (bool-val (zero? (expval->num val)))))
     (let-exp-cont
      (var body saved-env saved-cont)
      (value-of/k body (extend-env var (newref val) saved-env) saved-cont))
     (if-test-cont (exp2 exp3 saved-env saved-cont)
                   (if (expval->bool val)
                       (value-of/k exp2 saved-env saved-cont)
                       (value-of/k exp3 saved-env saved-cont)))
     (diff1-cont (exp2 env saved-cont) (value-of/k exp2 env (diff2-cont val saved-cont)))
     (diff2-cont (val1 saved-cont)
                 (let ([num1 (expval->num val1)] [num2 (expval->num val)])
                   (apply-cont saved-cont (num-val (- num1 num2)))))
     (rator-cont (rand env saved-cont) (value-of/k rand env (rand-cont val saved-cont)))
     (rand-cont (val1 saved-cont)
                (let ([proc1 (expval->proc val1)])
                  (apply-procedure/k proc1 val saved-cont)))
     (set-rhs-cont (var env saved-cont)
                   (begin
                     (setref! (apply-env env var) val)
                     (apply-cont saved-cont val)))
     (seq-cont
      (exps env saved-cont)
      (if (null? exps)
          (apply-cont saved-cont val)
          (value-of/k (car exps) env (seq-cont (cdr exps) env saved-cont)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter
(define init-env
  (lambda ()
    (extend-env 'true
                (newref (bool-val #t))
                (extend-env 'false (newref (bool-val #f)) (empty-env)))))

; value-of-program : Program → FinalAnswer
(define value-of-program
  (lambda (pgm)
    (initialize-store!)
    (cases program
           pgm
           (a-program (exp1) (value-of/k exp1 (init-env) (end-cont))))))

; value-of/k : Exp × Env × Cont → FinalAnswer
(define value-of/k
  (lambda (exp env cont)
    (cases
     expression
     exp
     (const-exp (num) (apply-cont cont (num-val num)))
     (var-exp (var) (apply-cont cont (deref (apply-env env var))))
     (assign-exp (var exp1) (value-of/k exp1 env (set-rhs-cont var env cont)))
     (proc-exp (var body) (apply-cont cont (proc-val (procedure var body env))))
     (letrec-exp
      (p-name b-var p-body letrec-body)
      (value-of/k letrec-body (extend-env-rec p-name b-var p-body env) cont))
     (zero?-exp (exp1) (value-of/k exp1 env (zero1-cont cont)))
     (if-exp (exp1 exp2 exp3)
             (value-of/k exp1 env (if-test-cont exp2 exp3 env cont)))
     (let-exp (var exp1 body)
              (value-of/k exp1 env (let-exp-cont var body env cont)))
     (diff-exp (exp1 exp2) (value-of/k exp1 env (diff1-cont exp2 env cont)))
     (call-exp (rator rand) (value-of/k rator env (rator-cont rand env cont)))
     (seq-exp (fst exps) (value-of/k fst env (seq-cont exps env cont))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; run
(define run (lambda (code) (value-of-program (scan&parse code))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; (trace value-of/k)
;;; test
(define str0
  "
  letrec double(x) = if zero?(x) then 0 else -((double -(x,1)), -2)
  in (double 6)
   ")
(check-equal? (run str0) (num-val 12))

(define str1 "
  letrec id(x) = x
  in (id 0)
   ")
(check-equal? (run str1) (num-val 0))

(define str2
  "let g = let counter = 0
           in proc (dummy)
                {
                  set counter = -(counter, -1);
                  counter
                }
  in let a = (g 11)
     in let b = (g 11)
        in -(a,b)")
(check-equal? (run str2) (num-val -1))

(define str4
  "let f = proc (x) proc (y)
            {
              set x = -(x,-1);
              -(x,y)
            }
  in ((f 44) 33)")
(check-equal? (run str4) (num-val 12))

(define str5 "let p = proc (x) set x = 4
   in let a = 3
   in { (p a); a }")
(check-equal? (run str5) (num-val 3))

(define str6 "let p = 114
   in let void = set p = -(514, p)
      in p
  ")
(check-equal? (run str6) (num-val 400))
