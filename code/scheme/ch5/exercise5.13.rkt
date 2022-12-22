#lang eopl
(require rackunit)
(require racket/trace)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Procedure data type
; procedure : Var × Exp × Env → Proc
(define-datatype proc
                 proc?
                 (procedure (name identifier?)
                            (vars (list-of identifier?))
                            (body expression?)
                            (saved-env environment?)))
; apply-procedure : Proc × ExpVal → ExpVal
; apply-procedure/k : Proc × ExpVal × Cont → FinalAnswer
(define apply-procedure/k
  (lambda (proc1 vals cont)
    (cases proc
           proc1
           (procedure (name vars body saved-env)
                      (begin
                        (trace name vals cont)
                        (value-of/k body
                                    (extend-env-vars-vals vars vals saved-env)
                                    cont))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal data type
(define-datatype expval
                 expval?
                 (num-val (value number?))
                 (bool-val (boolean boolean?))
                 (proc-val (proc proc?))
                 (pair-val (fst expval?) (snd expval?))
                 (nil-val))

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

(define expval->pair-fst
  (lambda (v)
    (cases expval
           v
           (pair-val (fst snd) fst)
           (else (eopl:error 'expval->pair-fst)))))

(define expval->pair-snd
  (lambda (v)
    (cases expval
           v
           (pair-val (fst snd) snd)
           (else (eopl:error 'expval->pair-snd)))))

(define expval->nil
  (lambda (v)
    (cases expval v (nil-val () 'nil) (else (eopl:error 'expval->nil)))))

(define nil? (lambda (v) (cases expval v (nil-val () #t) (else #f))))

(define pair-val?
  (lambda (v) (cases expval v (pair-val (fst snd) #t) (else #f))))

(define list->pair-vals
  (lambda (lst)
    (if (null? lst)
        (nil-val)
        (pair-val (car lst) (list->pair-vals (cdr lst))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Env
(define-datatype environment
                 environment?
                 (empty-env)
                 (extend-env (var identifier?) (val expval?) (env environment?))
                 (extend-env-rec (p-name identifier?)
                                 (b-vars (list-of identifier?))
                                 (body expression?)
                                 (env environment?)))

(define extend-env-vars-vals
  (lambda (vars vals env)
    (if (null? vars)
        env
        (extend-env (car vars)
                    (car vals)
                    (extend-env-vars-vals (cdr vars) (cdr vals) env)))))

(define apply-env
  (lambda (env search-var)
    (cases environment
           env
           (empty-env () (eopl:error 'apply-env))
           (extend-env (saved-var saved-val saved-env)
                       (if (eqv? saved-var search-var)
                           saved-val
                           (apply-env saved-env search-var)))
           (extend-env-rec (p-name b-vars p-body saved-env)
                           (if (eqv? search-var p-name)
                               (proc-val (procedure p-name b-vars p-body env))
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
 (diff-exp (exp1 expression?) (exp2 expression?))
 (mul-exp (exp1 expression?) (exp2 expression?))
 (let-exp (vars (list-of identifier?))
          (exps (list-of expression?))
          (body expression?))
 (let2-exp (var1 identifier?)
           (exp1 expression?)
           (var2 identifier?)
           (exp2 expression?)
           (body expression?))
 (let3-exp (var1 identifier?)
           (exp1 expression?)
           (var2 identifier?)
           (exp2 expression?)
           (var3 identifier?)
           (exp3 expression?)
           (body expression?))
 (letrec-exp (p-name identifier?)
             (b-vars (list-of identifier?))
             (p-body expression?)
             (letrec-body expression?))
 (proc-exp (vars (list-of identifier?)) (body expression?))
 (call-exp (rator expression?) (rand (list-of expression?)))
 (cons-exp (fst-exp expression?) (snd-exp expression?))
 (car-exp (pair-exp expression?))
 (cdr-exp (pair-exp expression?))
 (null?-exp (exp expression?))
 (nil-exp)
 (list-exp (exps (list-of expression?))))

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
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("*" "(" expression "," expression ")") mul-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression)
                let-exp)
    (expression ("let2" identifier
                        "="
                        expression
                        identifier
                        "="
                        expression
                        "in"
                        expression)
                let2-exp)
    (expression ("let3" identifier
                        "="
                        expression
                        identifier
                        "="
                        expression
                        identifier
                        "="
                        expression
                        "in"
                        expression)
                let3-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("null?" "(" expression ")") null?-exp)
    (expression ("emptylist") nil-exp)
    (expression ("letrec" identifier
                          "("
                          (arbno identifier)
                          ")"
                          "="
                          expression
                          "in"
                          expression)
                letrec-exp)
    (expression ("proc" "(" (separated-list identifier ",") ")" expression)
                proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("list" "(" (separated-list expression ",") ")") list-exp)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar-spec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;Continuation
(define-datatype
 continuation
 continuation?
 (end-cont)
 (zero1-cont (cont continuation?))
 (let-exp-cont (vars (list-of identifier?))
               (exps (list-of expression?))
               (vals (list-of expval?))
               (body expression?)
               (env environment?)
               (cont continuation?))
 (let2-exp1-cont (var1 identifier?)
                 (var2 identifier?)
                 (exp2 expression?)
                 (body expression?)
                 (env environment?)
                 (cont continuation?))
 (let2-exp2-cont (var2 identifier?)
                 (body expression?)
                 (env environment?)
                 (cont continuation?))
 (let3-exp1-cont (var1 identifier?)
                 (var2 identifier?)
                 (var3 identifier?)
                 (exp2 expression?)
                 (exp3 expression?)
                 (body expression?)
                 (env environment?)
                 (cont continuation?))
 (let3-exp2-cont (var2 identifier?)
                 (var3 identifier?)
                 (exp3 expression?)
                 (body expression?)
                 (env environment?)
                 (cont continuation?))
 (let3-exp3-cont (var3 identifier?)
                 (body expression?)
                 (env environment?)
                 (cont continuation?))
 (if-test-cont (exp2 expression?)
               (exp3 expression?)
               (env environment?)
               (cont continuation?))
 (diff1-cont (exp2 expression?) (env environment?) (cont continuation?))
 (diff2-cont (val1 expval?) (cont continuation?))
 (mul1-cont (exp2 expression?) (env environment?) (cont continuation?))
 (mul2-cont (val1 expval?) (cont continuation?))
 (rator-cont (rands (list-of expression?))
             (env environment?)
             (cont continuation?))
 (rands-cont (p expval?)
             (rands (list-of expression?))
             (vals (list-of expval?))
             (env environment?)
             (cont continuation?))
 (cons-fst-cont (snd-exp expression?) (env environment?) (cont continuation?))
 (cons-snd-cont (val1 expval?) (cont continuation?))
 (car-cont (cont continuation?))
 (cdr-cont (cont continuation?))
 (null?-cont (cont continuation?))
 (list-cont (exps (list-of expression?))
            (vals (list-of expval?))
            (env environment?)
            (cont continuation?)))

; apply-cont : Cont × ExpVal → FinalAnswer
(define apply-cont
  (lambda (cont val)
    (cases
     continuation
     cont
     (end-cont ()
               (begin
                 (eopl:printf "End of computation.~%")
                 val))
     (zero1-cont (saved-cont)
                 (apply-cont saved-cont (bool-val (zero? (expval->num val)))))
     (let-exp-cont
      (vars exps vals body env saved-cont)
      (if (null? exps)
          (value-of/k body
                      (extend-env-vars-vals vars (reverse (cons val vals)) env)
                      saved-cont)
          (value-of/k
           (car exps)
           env
           (let-exp-cont vars (cdr exps) (cons val vals) body env saved-cont))))
     (let2-exp1-cont
      (var1 var2 exp2 body saved-env cont)
      (let ([new-env (extend-env var1 val saved-env)])
        (value-of/k exp2 new-env (let2-exp2-cont var2 body new-env cont))))
     (let2-exp2-cont (var2 body saved-env cont)
                     (value-of/k body (extend-env var2 val saved-env) cont))
     (let3-exp1-cont
      (var1 var2 var3 exp2 exp3 body env cont)
      (let ([new-env (extend-env var1 val env)])
        (value-of/k exp2
                    new-env
                    (let3-exp2-cont var2 var3 exp3 body new-env cont))))
     (let3-exp2-cont
      (var2 var3 exp3 body env cont)
      (let ([new-env (extend-env var2 val env)])
        (value-of/k exp3 new-env (let3-exp3-cont var3 body new-env cont))))
     (let3-exp3-cont (var3 body env cont)
                     (value-of/k body (extend-env var3 val env) cont))
     (if-test-cont (exp2 exp3 saved-env saved-cont)
                   (if (expval->bool val)
                       (value-of/k exp2 saved-env saved-cont)
                       (value-of/k exp3 saved-env saved-cont)))
     (diff1-cont (exp2 env cont) (value-of/k exp2 env (diff2-cont val cont)))
     (diff2-cont (val1 cont)
                 (let ([num1 (expval->num val1)] [num2 (expval->num val)])
                   (apply-cont cont (num-val (- num1 num2)))))
     (mul1-cont (exp2 env cont) (value-of/k exp2 env (mul2-cont val cont)))
     (mul2-cont (val1 cont)
                (let ([num1 (expval->num val1)] [num2 (expval->num val)])
                  (apply-cont cont (num-val (* num1 num2)))))
     (rator-cont (rands env cont)
                 (if (null? rands)
                     (apply-procedure/k (expval->proc val) '() cont)
                     (value-of/k (car rands)
                                 env
                                 (rands-cont val (cdr rands) '() env cont))))
     (rands-cont
      (p rands vals env cont)
      (let ([new-vals (cons val vals)])
        (if (null? rands)
            (apply-procedure/k (expval->proc p) (reverse new-vals) cont)
            (value-of/k (car rands)
                        env
                        (rands-cont p (cdr rands) new-vals env cont)))))
     (cons-fst-cont (snd-exp env cont)
                    (value-of/k snd-exp env (cons-snd-cont val cont)))
     (cons-snd-cont (val1 cont) (apply-cont cont (pair-val val1 val)))
     (car-cont (cont)
               (let ([fst (expval->pair-fst val)]) (apply-cont cont fst)))
     (cdr-cont (cont)
               (let ([fst (expval->pair-snd val)]) (apply-cont cont fst)))
     (null?-cont (cont) (apply-cont cont (bool-val (nil? val))))
     (list-cont
      (exps vals env cont)
      (if (null? exps)
          (apply-cont cont (list->pair-vals (reverse (cons val vals))))
          (value-of/k (car exps)
                      env
                      (list-cont (cdr exps) (cons val vals) env cont)))))))
(define size-cont
  (lambda (cont)
    (cases
     continuation
     cont
     (end-cont () 0)
     (zero1-cont (cont) (+ 1 (size-cont cont)))
     (let-exp-cont (vars exps vals body env cont) (+ 1 (size-cont cont)))
     (let2-exp1-cont (var1 var2 exp2 body saved-env cont)
                     (+ 1 (size-cont cont)))
     (let2-exp2-cont (var2 body saved-env cont) (+ 1 (size-cont cont)))
     (let3-exp1-cont (var1 var2 var3 exp2 exp3 body env cont)
                     (+ 1 (size-cont cont)))
     (let3-exp2-cont (var2 var3 exp3 body env cont) (+ 1 (size-cont cont)))
     (let3-exp3-cont (var3 body env cont) (+ 1 (size-cont cont)))
     (if-test-cont (exp2 exp3 saved-env cout) (+ 1 (size-cont cont)))
     (diff1-cont (exp2 env cont) (+ 1 (size-cont cont)))
     (diff2-cont (val1 cont) (+ 1 (size-cont cont)))
     (mul1-cont (exp2 env cont) (+ 1 (size-cont cont)))
     (mul2-cont (val1 cont) (+ 1 (size-cont cont)))
     (rator-cont (rands env cont) (+ 1 (size-cont cont)))
     (rands-cont (p rands vals env cont) (+ 1 (size-cont cont)))
     (cons-fst-cont (snd-exp env cont) (+ 1 (size-cont cont)))
     (cons-snd-cont (val1 cont) (+ 1 (size-cont cont)))
     (car-cont (cont) (+ 1 (size-cont cont)))
     (cdr-cont (cont) (+ 1 (size-cont cont)))
     (null?-cont (cont) (+ 1 (size-cont cont)))
     (list-cont (exps vals env cont) (+ 1 (size-cont cont))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Trace
(define trace? #t)

(define trace
  (lambda (name vals cont)
    (if trace? (trace-show name vals cont (size-cont cont)) '())))
(define trace-show
  (lambda (name vals cont depth)
    (if (= 0 depth)
        (begin
          (display name)
          (display " ")
          (display vals)
          (display " ")
          ;    (display cont)
        ;   (newline)
          (newline))
        (begin
          (display ">")
          (trace-show name vals cont (- depth 1))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter
(define init-env
  (lambda ()
    (extend-env 'true
                (bool-val #t)
                (extend-env 'false (bool-val #f) (empty-env)))))

; value-of-program : Program → FinalAnswer
(define value-of-program
  (lambda (pgm)
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
     (var-exp (var) (apply-cont cont (apply-env env var)))
     (proc-exp (vars body)
               (apply-cont cont (proc-val (procedure '<proc> vars body env))))
     (letrec-exp
      (p-name b-vars p-body letrec-body)
      (value-of/k letrec-body (extend-env-rec p-name b-vars p-body env) cont))
     (zero?-exp (exp1) (value-of/k exp1 env (zero1-cont cont)))
     (if-exp (exp1 exp2 exp3)
             (value-of/k exp1 env (if-test-cont exp2 exp3 env cont)))
     (let-exp (vars exps body)
              (if (null? vars)
                  (value-of/k body env cont)
                  (value-of/k
                   (car exps)
                   env
                   (let-exp-cont vars (cdr exps) '() body env cont))))
     (let2-exp
      (var1 exp1 var2 exp2 body)
      (value-of/k exp1 env (let2-exp1-cont var1 var2 exp2 body env cont)))
     (let3-exp (var1 exp1 var2 exp2 var3 exp3 body)
               (value-of/k
                exp1
                env
                (let3-exp1-cont var1 var2 var3 exp2 exp3 body env cont)))
     (diff-exp (exp1 exp2) (value-of/k exp1 env (diff1-cont exp2 env cont)))
     (mul-exp (exp1 exp2) (value-of/k exp1 env (mul1-cont exp2 env cont)))
     (call-exp (rator rand) (value-of/k rator env (rator-cont rand env cont)))
     (cons-exp (fst-exp snd-exp)
               (value-of/k fst-exp env (cons-fst-cont snd-exp env cont)))
     (car-exp (pair-exp) (value-of/k pair-exp env (car-cont cont)))
     (cdr-exp (pair-exp) (value-of/k pair-exp env (cdr-cont cont)))
     (null?-exp (expr) (value-of/k expr env (null?-cont cont)))
     (nil-exp () (apply-cont cont (nil-val)))
     (list-exp (exps)
               (if (null? exps)
                   (apply-cont cont (nil-val))
                   (value-of/k (car exps)
                               env
                               (list-cont (cdr exps) (list) env cont)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; run
(define run (lambda (code) (value-of-program (scan&parse code))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; (trace value-of/k)
;;; test
(define code1 "
  cons (-(0, 114), -(51, 4))
  ")
; (check-equal? (run code1) (pair-val (num-val -114) (num-val 47)))

(define code2 "
  let p = cons (-(0, 114), -(51, 4))
  in car(p)
  ")
; (check-equal? (run code2) (num-val -114))

(define code3 "
  let p = cons (-(0, 114), -(51, 4))
  in cdr(p)
  ")
; (check-equal? (run code3) (num-val 47))

(define code4
  "
  let foo = cons (-(0, 114), -(51, 4))
  in if null?(foo)
     then 114
     else 514
  ")
; (check-equal? (run code4) (num-val 514))

(define code5
  "
  let foo = cons (-(0, 114), emptylist)
  in if null?(cdr(foo))
     then 114
     else 514
  ")
; (check-equal? (run code5) (num-val 114))

(define code6 "
  let x = 4
  in list(x, -(x,1), -(x,3))
 ")
; (check-equal? (run code6) (pair-val (num-val 4) (pair-val (num-val 3) (pair-val (num-val 1) (nil-val)))))

(define code7
  "
  let x = 114
      y = 51
      z = 4
  in -(x, -(0, -(y, -(0, z))))
  ")
; (check-equal? (run code7) (num-val 169))

(define code8
  "
  let a = 114
      b = 514
      c = 114514
      sum = proc(x, y, z) -(x, -(0, -(y, -(0, z))))
  in (sum a b c)
  ")
; (check-equal? (run code8) (num-val 115142))

(define code9 "
      let foo = proc() 114514
      in (foo)
      ")
; (check-equal? (run code9) (num-val 114514))

(define code10
  "
  letrec fact(n) = if zero?(n) then 1 else *(n, (fact -(n, 1)))
  in (fact 10)
  ")
(check-equal? (run code10) (num-val 3628800))

(define code11
  "
  letrec fact-iter-acc(n a) = if zero?(n) then a else (fact-iter-acc -(n, 1) *(n, a))
  in letrec fact-iter(n) = (fact-iter-acc n 1)
     in (fact-iter 10)
 ")
(check-equal? (run code11) (num-val 3628800))
