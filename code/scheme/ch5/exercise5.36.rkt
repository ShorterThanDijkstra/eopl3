#lang eopl
(require rackunit)
(require racket/trace)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Procedure data type
(define-datatype
 proc
 proc?
 (procedure (var identifier?) (body expression?) (saved-env environment?)))
(define apply-procedure/k
  (lambda (proc1 val cont ex-handler)
    (cases proc
           proc1
           (procedure
            (var body saved-env)
            (value-of/k body (extend-env var val saved-env) cont ex-handler)))))

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
                                 (b-var identifier?)
                                 (body expression?)
                                 (env environment?)))

(define apply-env
  (lambda (env search-var)
    (cases environment
           env
           (empty-env () (eopl:error 'apply-env))
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
 (let-exp (var identifier?) (exp expression?) (body expression?))
 (letrec-exp (p-name identifier?)
             (b-var identifier?)
             (p-body expression?)
             (letrec-body expression?))
 (proc-exp (var identifier?) (body expression?))
 (call-exp (rator expression?) (rand expression?))
 (cons-exp (fst-exp expression?) (snd-exp expression?))
 (car-exp (pair-exp expression?))
 (cdr-exp (pair-exp expression?))
 (null?-exp (exp expression?))
 (nil-exp)
 (list-exp (exps (list-of expression?)))
 (try-exp (exp1 expression?) (var identifier?) (handler-exp expression?))
 (raise-exp (exp1 expression?)))

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
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("null?" "(" expression ")") null?-exp)
    (expression ("emptylist") nil-exp)
    (expression
     ("letrec" identifier "(" identifier ")" "=" expression "in" expression)
     letrec-exp)
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    (expression ("(" expression expression ")") call-exp)
    (expression ("list" "(" (separated-list expression ",") ")") list-exp)
    (expression ("try" expression "catch" "(" identifier ")" expression)
                try-exp)
    (expression ("raise" expression) raise-exp)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar-spec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Exception
(define report-uncaught-exception
  (lambda () (eopl:printf "Uncaught Exception.~%")))

(define apply-handler
  (lambda (val ex-handler)
    (cases continuation
           ex-handler
           (try-cont (var handler-exp saved-env saved-cont former-ex-handler)
                     (value-of/k handler-exp
                                 (extend-env var val saved-env)
                                 saved-cont
                                 former-ex-handler))
           (else (report-uncaught-exception)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;Continuation
(define-datatype
 continuation
 continuation?
 (end-cont)
 (zero1-cont (saved-cont continuation?))
 (let-exp-cont (var identifier?)
               (body expression?)
               (env environment?)
               (cont continuation?))
 (if-test-cont (exp2 expression?)
               (exp3 expression?)
               (env environment?)
               (saved-cont continuation?))
 (diff1-cont (exp2 expression?) (env environment?) (saved-cont continuation?))
 (diff2-cont (val1 expval?) (saved-cont continuation?))
 (rator-cont (rand expression?) (env environment?) (saved-cont continuation?))
 (rand-cont (val1 expval?) (saved-cont continuation?))
 (cons-fst-cont (snd-exp expression?)
                (env environment?)
                (saved-cont continuation?))
 (cons-snd-cont (val1 expval?) (saved-cont continuation?))
 (car-cont (saved-cont continuation?))
 (cdr-cont (saved-cont continuation?))
 (null?-cont (saved-cont continuation?))
 (list-cont (exps (list-of expression?))
            (vals (list-of expval?))
            (env environment?)
            (saved-cont continuation?))
 (try-cont (var identifier?)
           (handler-exp expression?)
           (env environment?)
           (saved-cont continuation?)
           (former-ex-handler continuation?))
 (raise1-cont (saved-cont continuation?)))

(define apply-cont
  (lambda (cont val ex-handler)
    (cases
     continuation
     cont
     (end-cont ()
               (begin
                 (eopl:printf "End of computation.~%")
                 val))
     (zero1-cont
      (saved-cont)
      (apply-cont saved-cont (bool-val (zero? (expval->num val))) ex-handler))
     (let-exp-cont
      (var body saved-env saved-cont)
      (value-of/k body (extend-env var val saved-env) saved-cont ex-handler))
     (if-test-cont (exp2 exp3 saved-env saved-cont)
                   (if (expval->bool val)
                       (value-of/k exp2 saved-env saved-cont ex-handler)
                       (value-of/k exp3 saved-env saved-cont ex-handler)))
     (diff1-cont (exp2 env saved-cont)
                 (value-of/k exp2 env (diff2-cont val saved-cont) ex-handler))
     (diff2-cont (val1 saved-cont)
                 (let ([num1 (expval->num val1)] [num2 (expval->num val)])
                   (apply-cont saved-cont (num-val (- num1 num2)) ex-handler)))
     (rator-cont (rand env saved-cont)
                 (value-of/k rand env (rand-cont val saved-cont) ex-handler))
     (rand-cont (val1 saved-cont)
                (let ([proc1 (expval->proc val1)])
                  (apply-procedure/k proc1 val saved-cont ex-handler)))
     (cons-fst-cont
      (snd-exp env saved-cont)
      (value-of/k snd-exp env (cons-snd-cont val saved-cont) ex-handler))
     (cons-snd-cont (val1 saved-cont)
                    (apply-cont saved-cont (pair-val val1 val) ex-handler))
     (car-cont (saved-cont)
               (let ([fst (expval->pair-fst val)])
                 (apply-cont saved-cont fst ex-handler)))
     (cdr-cont (saved-cont)
               (let ([fst (expval->pair-snd val)])
                 (apply-cont saved-cont fst ex-handler)))
     (null?-cont (saved-cont)
                 (apply-cont saved-cont (bool-val (nil? val)) ex-handler))
     (list-cont (exps vals env saved-cont)
                (if (null? exps)
                    (apply-cont saved-cont
                                (list->pair-vals (reverse (cons val vals)))
                                ex-handler)
                    (value-of/k
                     (car exps)
                     env
                     (list-cont (cdr exps) (cons val vals) env saved-cont)
                     ex-handler)))
     (try-cont (var handler-exp env saved-cont former-ex-handler)
               (apply-cont saved-cont val ex-handler))
     (raise1-cont (saved-cont) (apply-handler val ex-handler)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter
(define init-env
  (lambda ()
    (extend-env 'true
                (bool-val #t)
                (extend-env 'false (bool-val #f) (empty-env)))))

(define value-of-program
  (lambda (pgm)
    (cases program
           pgm
           (a-program (exp1)
                      (value-of/k exp1 (init-env) (end-cont) (end-cont))))))

(define value-of/k
  (lambda (exp env cont ex-handler)
    (cases
     expression
     exp
     (const-exp (num) (apply-cont cont (num-val num) ex-handler))
     (var-exp (var) (apply-cont cont (apply-env env var) ex-handler))
     (proc-exp (var body)
               (apply-cont cont (proc-val (procedure var body env)) ex-handler))
     (letrec-exp (p-name b-var p-body letrec-body)
                 (value-of/k letrec-body
                             (extend-env-rec p-name b-var p-body env)
                             cont
                             ex-handler))
     (zero?-exp (exp1) (value-of/k exp1 env (zero1-cont cont) ex-handler))
     (if-exp (exp1 exp2 exp3)
             (value-of/k exp1 env (if-test-cont exp2 exp3 env cont) ex-handler))
     (let-exp (var exp1 body)
              (value-of/k exp1 env (let-exp-cont var body env cont) ex-handler))
     (diff-exp (exp1 exp2)
               (value-of/k exp1 env (diff1-cont exp2 env cont) ex-handler))
     (call-exp (rator rand)
               (value-of/k rator env (rator-cont rand env cont) ex-handler))
     (cons-exp
      (fst-exp snd-exp)
      (value-of/k fst-exp env (cons-fst-cont snd-exp env cont) ex-handler))
     (car-exp (pair-exp) (value-of/k pair-exp env (car-cont cont) ex-handler))
     (cdr-exp (pair-exp) (value-of/k pair-exp env (cdr-cont cont) ex-handler))
     (null?-exp (expr) (value-of/k expr env (null?-cont cont) ex-handler))
     (nil-exp () (apply-cont cont (nil-val) ex-handler))
     (list-exp (exps)
               (if (null? exps)
                   (apply-cont cont (nil-val) ex-handler)
                   (value-of/k (car exps)
                               env
                               (list-cont (cdr exps) (list) env cont)
                               ex-handler)))
     (try-exp (exp1 var handler-exp)
              (let ([new-ex-handler
                     (try-cont var handler-exp env cont ex-handler)])
                (value-of/k exp1 env new-ex-handler new-ex-handler)))
     (raise-exp (exp1) (value-of/k exp1 env (raise1-cont cont) ex-handler)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; run
(define run (lambda (code) (value-of-program (scan&parse code))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; (trace value-of/k)

;;; test
(define code1
  "let index = proc (n)
                 letrec inner (lst)
                          = if null?(lst)
                            then raise 99
                            else if zero?(-(car(lst), n))
                                 then 0
                                 else -((inner cdr(lst)), -1)
                 in proc (lst)
                      try (inner lst)
                      catch (x) -1
  in ((index 5) list(2, 3))")
(check-equal? (run code1) (num-val -1))

(define code2
  "let index = proc (n)
                 letrec inner (lst)
                          = if null?(lst)
                            then raise -1
                            else if zero?(-(car(lst), n))
                                 then 0
                                 else -((inner cdr(lst)), -1)
                 in proc (lst)
                      try (inner lst)
                      catch (x) -1
  in ((index 5) list(2, 7, 11, 71, 5))")
(check-equal? (run code2) (num-val 4))

(define code3
  "let index = proc (n)
                 letrec inner (lst)
                          = if null?(lst)
                            then raise -1
                            else if zero?(-(car(lst), n))
                                 then 0
                                 else -((inner cdr(lst)), -1)
                 in proc (lst)
                      (inner lst)
  in ((index 5) list(2, 7, 11, 71, 51))")
(run code3)


(define code4
  "let foo = proc(dummy) raise -1
   in let bar = proc(dummy) try (foo 0) catch(e) raise -2
      in let baz = proc(dummy) try (bar 0) catch(e) raise -3
         in try (baz 0) catch(e) e")
(check-equal? (run code4) (num-val -3))
