#lang eopl
(require rackunit)
(require racket/trace)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Procedure data type
(define-datatype proc
                 proc?
                 (procedure (vars (list-of identifier?))
                            (body expression?)
                            (saved-env environment?)))
(define apply-procedure/k
  (lambda (proc1 vals cont)
    (cases proc
           proc1
           (procedure
            (vars body saved-env)
            (value-of/k body (extend-env-vars vars vals saved-env) cont)))))

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

(define extend-env-vars
  (lambda (vars vals env)
    (if (null? vars)
        env
        (extend-env (car vars)
                    (car vals)
                    (extend-env-vars (cdr vars) (cdr vals) env)))))
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
                               (proc-val (procedure b-vars p-body env))
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
             (b-vars (list-of identifier?))
             (p-body expression?)
             (letrec-body expression?))
 (proc-exp (vars (list-of identifier?)) (body expression?))
 (call-exp (rator expression?) (rands (list-of expression?)))
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
    (expression ("letrec" identifier
                          "("
                          (separated-list identifier ",")
                          ")"
                          "="
                          expression
                          "in"
                          expression)
                letrec-exp)
    (expression ("proc" "(" (separated-list identifier ",") ")" expression)
                proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("list" "(" (separated-list expression ",") ")") list-exp)
    (expression ("try" expression "catch" "(" identifier ")" expression)
                try-exp)
    (expression ("raise" expression) raise-exp)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar-spec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;Continuation

(define report-uncaught-exception
  (lambda () (eopl:printf "Uncaught Exception.~%")))

(define end-cont
  (lambda ()
    (let ([cont-apply (lambda (val)
                        (begin
                          (eopl:printf "End of computation.~%")
                          val))]
          [handler-apply (lambda () 'end-cont)])
      (list cont-apply handler-apply))))

(define zero1-cont
  (lambda (saved-cont)
    (let ([cont-apply (lambda (val)
                        (apply-cont saved-cont
                                    (bool-val (zero? (expval->num val)))))]
          [handler-apply (lambda () saved-cont)])
      (list cont-apply handler-apply))))

(define let-exp-cont
  (lambda (var body saved-env saved-cont)
    (let ([cont-apply
           (lambda (val)
             (value-of/k body (extend-env var val saved-env) saved-cont))]
          [handler-apply (lambda () saved-cont)])
      (list cont-apply handler-apply))))

(define if-test-cont
  (lambda (exp2 exp3 saved-env saved-cont)
    (let ([cont-apply (lambda (val)
                        (if (expval->bool val)
                            (value-of/k exp2 saved-env saved-cont)
                            (value-of/k exp3 saved-env saved-cont)))]
          [handler-apply (lambda () saved-cont)])
      (list cont-apply handler-apply))))

(define diff1-cont
  (lambda (exp2 saved-env saved-cont)
    (let ([cont-apply
           (lambda (val)
             (value-of/k exp2 saved-env (diff2-cont val saved-cont)))]
          [handler-apply (lambda () saved-cont)])
      (list cont-apply handler-apply))))

(define diff2-cont
  (lambda (val1 saved-cont)
    (let ([cont-apply
           (lambda (val)
             (let ([num1 (expval->num val1)] [num2 (expval->num val)])
               (apply-cont saved-cont (num-val (- num1 num2)))))]
          [handler-apply (lambda () saved-cont)])
      (list cont-apply handler-apply))))

(define rator-cont
  (lambda (rands saved-env saved-cont)
    (let ([cont-apply
           (lambda (val)
             (if (null? rands)
                 (apply-procedure/k (expval->proc val) '() saved-cont)
                 (value-of/k
                  (car rands)
                  saved-env
                  (rands-cont val (cdr rands) '() saved-env saved-cont))))]
          [handler-apply (lambda () saved-cont)])
      (list cont-apply handler-apply))))

(define rands-cont
  (lambda (proc1 rands vals saved-env saved-cont)
    (let ([cont-apply (lambda (val)
                        (let ([new-vals (cons val vals)])
                          (if (null? rands)
                              (apply-procedure/k (expval->proc proc1)
                                                 (reverse new-vals)
                                                 saved-cont)
                              (value-of/k (car rands)
                                          saved-env
                                          (rands-cont proc1
                                                      (cdr rands)
                                                      new-vals
                                                      saved-env
                                                      saved-cont)))))]
          [handler-apply (lambda () saved-cont)])
      (list cont-apply handler-apply))))

(define cons-fst-cont
  (lambda (snd-exp saved-env saved-cont)
    (let ([cont-apply
           (lambda (val)
             (value-of/k snd-exp saved-env (cons-snd-cont val saved-cont)))]
          [handler-apply (lambda () saved-cont)])
      (list cont-apply handler-apply))))

(define cons-snd-cont
  (lambda (val1 saved-cont)
    (let ([cont-apply (lambda (val)
                        (apply-cont saved-cont (pair-val val1 val)))]
          [handler-apply (lambda () saved-cont)])
      (list cont-apply handler-apply))))

(define car-cont
  (lambda (saved-cont)
    (let ([cont-apply (lambda (val)
                        (let ([fst (expval->pair-fst val)])
                          (apply-cont saved-cont fst)))]
          [handler-apply (lambda () saved-cont)])
      (list cont-apply handler-apply))))

(define cdr-cont
  (lambda (saved-cont)
    (let ([cont-apply (lambda (val)
                        (let ([snd (expval->pair-snd val)])
                          (apply-cont saved-cont snd)))]
          [handler-apply (lambda () saved-cont)])
      (list cont-apply handler-apply))))

(define null?-cont
  (lambda (saved-cont)
    (let ([cont-apply (lambda (val)
                        (apply-cont saved-cont (bool-val (nil? val))))]
          [handler-apply (lambda () saved-cont)])
      (list cont-apply handler-apply))))

(define list-cont
  (lambda (exps vals saved-env saved-cont)
    (let ([cont-apply (lambda (val)
                        (if (null? exps)
                            (apply-cont saved-cont
                                        (list->pair-vals
                                         (reverse (cons val vals))))
                            (value-of/k (car exps)
                                        saved-env
                                        (list-cont (cdr exps)
                                                   (cons val vals)
                                                   saved-env
                                                   saved-cont))))]
          [handler-apply (lambda () saved-cont)])
      (list cont-apply handler-apply))))

(define try-cont
  (lambda (var handler-exp saved-env saved-cont)
    (let ([cont-apply (lambda (val) (apply-cont saved-cont val))]
          [handler-apply
           (lambda () (list 'try-cont var handler-exp saved-env saved-cont))])
      (list cont-apply handler-apply))))

(define raise1-cont
  (lambda (saved-cont)
    (let ([cont-apply (lambda (val) (apply-handler val saved-cont))]
          [handler-apply (lambda () saved-cont)])
      (list cont-apply handler-apply))))

(define apply-cont (lambda (cont val) ((car cont) val)))

(define try-cont?
  (lambda (cont)
    (and (list? cont) (= (length cont) 5) (eqv? (car cont) 'try-cont))))

(define end-cont? (lambda (v) (eqv? v 'end-cont)))

(define apply-handler
  (lambda (val cont)
    (let ([new-cont ((cadr cont))])
      (cond
        [(end-cont? new-cont) (report-uncaught-exception)]
        [(try-cont? new-cont)
         (let* ([var (cadr new-cont)]
                [handler-exp (caddr new-cont)]
                [saved-env (cadddr new-cont)]
                [saved-cont (car (cddddr new-cont))])
           (value-of/k handler-exp (extend-env var val saved-env) saved-cont))]
        [else (apply-handler val new-cont)]))))


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
           (a-program (exp1) (value-of/k exp1 (init-env) (end-cont))))))

(define value-of/k
  (lambda (exp env cont)
    (cases
     expression
     exp
     (const-exp (num) (apply-cont cont (num-val num)))
     (var-exp (var) (apply-cont cont (apply-env env var)))
     (proc-exp (vars body)
               (apply-cont cont (proc-val (procedure vars body env))))
     (letrec-exp
      (p-name b-vars p-body letrec-body)
      (value-of/k letrec-body (extend-env-rec p-name b-vars p-body env) cont))
     (zero?-exp (exp1) (value-of/k exp1 env (zero1-cont cont)))
     (if-exp (exp1 exp2 exp3)
             (value-of/k exp1 env (if-test-cont exp2 exp3 env cont)))
     (let-exp (var exp1 body)
              (value-of/k exp1 env (let-exp-cont var body env cont)))
     (diff-exp (exp1 exp2) (value-of/k exp1 env (diff1-cont exp2 env cont)))
     (call-exp (rator rands) (value-of/k rator env (rator-cont rands env cont)))
     (cons-exp (fst-exp snd-exp)
               (value-of/k fst-exp env (cons-fst-cont snd-exp env cont)))
     (car-exp (pair-exp) (value-of/k pair-exp env (car-cont cont)))
     (cdr-exp (pair-exp) (value-of/k pair-exp env (cdr-cont cont)))
     (null?-exp (expr) (value-of/k expr env (null?-cont cont)))
     (nil-exp () (apply-cont cont (nil-val)))
     (list-exp
      (exps)
      (if (null? exps)
          (apply-cont cont (nil-val))
          (value-of/k (car exps) env (list-cont (cdr exps) (list) env cont))))
     (try-exp (exp1 var handler-exp)
              (value-of/k exp1 env (try-cont var handler-exp env cont)))
     (raise-exp (exp1) (value-of/k exp1 env (raise1-cont cont))))))

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
(define code5
  "
  let sum = proc(x, y, z) -(x, -(0, -(y, -(0, z))))
  in (sum 114 514 114514)
  ")
(check-equal? (run code5) (num-val 115142))

(define code6 "
      let foo = proc() 114514
      in (foo)
      ")
(check-equal? (run code6) (num-val 114514))

(define code7
  "
  letrec double(x)
          = if zero?(x) then 0 else -((double -(x,1)), -2)
  in (double 6)
   ")
(check-equal? (run code7) (num-val 12))

(define code8 "
  try let x = raise 114
      in -(x, 514)
  catch (e) e
  ")
(check-equal? (run code8) (num-val 114))
