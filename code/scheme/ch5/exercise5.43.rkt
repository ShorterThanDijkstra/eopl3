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
    (cond [(cont-val? proc1)
           (apply-cont (expval->cont proc1) (car vals))]
          [(proc-val? proc1)
           (cases proc
             (expval->proc proc1)
             (procedure
              (vars body saved-env)
              (value-of/k body (extend-env-vars vars vals saved-env) cont)))]
          [else (eopl:error 'apply-procedure/k)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal data type
(define-datatype expval
  expval?
  (num-val (value number?))
  (bool-val (boolean boolean?))
  (proc-val (proc proc?))
  (pair-val (fst expval?) (snd expval?))
  (cont-val (cont continuation?))
  (nil-val))

(define expval->num
  (lambda (v)
    (cases expval
      v
      (num-val (num) num)
      (else (eopl:error 'expval->num "~s" v)))))

(define expval->cont
  (lambda (v)
    (cases expval
      v
      (cont-val (cont) cont)
      (else (eopl:error 'expval->cont "~s" v)))))

(define cont-val?
  (lambda (v)
    (cases expval
      v
      (cont-val (_) #t)
      (else #f))))

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

(define proc-val?
  (lambda (v)
    (cases expval
      v
      (proc-val (_) #t)
      (else #f))))

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
  (try-exp (exp1 expression?)
           (var1 identifier?)
           (var2 identifier?)
           (handler-exp expression?))
  (raise-exp (exp1 expression?))
  (call-cont-exp (var identifier?) (exp1 expression?))
  (letcc-exp (var identifier?) (body expression?))
  (throw-exp (exp1 expression?) (exp2 expression?))
  )

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
    (expression
     ("try" expression "catch" "(" identifier "," identifier ")" expression)
     try-exp)
    (expression ("raise" expression) raise-exp)
    (expression ("call-cont" identifier expression) call-cont-exp)
    (expression ("letcc" identifier "in" expression) letcc-exp)
    (expression ("throw" expression "to" expression) throw-exp)
    ))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar-spec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Exception
(define report-uncaught-exception
  (lambda () (eopl:printf "Uncaught Exception.~%")))

(define apply-handler
  (lambda (val cont raise2-cont)
    (cases
        continuation
      cont
      (try-cont (var1 var2 handler-exp saved-env saved-cont)
                (value-of/k handler-exp
                            (extend-env var2
                                        (cont-val raise2-cont)
                                        (extend-env var1 val saved-env))
                            saved-cont))
      (end-cont () (report-uncaught-exception))
      (zero1-cont (saved-cont) (apply-handler val saved-cont raise2-cont))
      (let-exp-cont (var body saved-env saved-cont)
                    (apply-handler val saved-cont raise2-cont))
      (if-test-cont (exp2 exp3 saved-env saved-cont)
                    (apply-handler val saved-cont raise2-cont))
      (diff1-cont (exp2 env saved-cont)
                  (apply-handler val saved-cont raise2-cont))
      (diff2-cont (val1 saved-cont) (apply-handler val saved-cont raise2-cont))
      (rator-cont (rands env saved-cont)
                  (apply-handler val saved-cont raise2-cont))
      (rands-cont (proc1 rands val1 env saved-cont)
                  (apply-handler val saved-cont raise2-cont))
      (cons-fst-cont (snd-exp env saved-cont)
                     (apply-handler val saved-cont raise2-cont))
      (cons-snd-cont (val1 saved-cont)
                     (apply-handler val saved-cont raise2-cont))
      (car-cont (saved-cont) (apply-handler val saved-cont raise2-cont))
      (cdr-cont (saved-cont) (apply-handler val saved-cont raise2-cont))
      (null?-cont (saved-cont) (apply-handler val saved-cont raise2-cont))
      (list-cont (exps vals env saved-cont)
                 (apply-handler val saved-cont raise2-cont))
      (raise1-cont (saved-cont) (apply-handler val saved-cont raise2-cont))
      (call-cont-cont (rator saved-cont)
                      (apply-handler val saved-cont raise2-cont))
      (throw-exp1-cont (exp2 env saved-cont) (apply-handler val saved-cont raise2-cont))
      (throw-exp2-cont (val1 saved-cont) (apply-handler val saved-cont raise2-cont))
      )))

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
  (rator-cont (rands (list-of expression?))
              (env environment?)
              (saved-cont continuation?))
  (rands-cont (proc1 expval?)
              (rands (list-of expression?))
              (vals (list-of expval?))
              (env environment?)
              (saved-cont continuation?))
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
  (try-cont (var1 identifier?)
            (var2 identifier?)
            (handler-exp expression?)
            (env environment?)
            (saved-cont continuation?))
  (raise1-cont (saved-cont continuation?))
  (call-cont-cont (rator continuation?) (saved-cont continuation?))
  (throw-exp1-cont (exp2 expression?)  (env environment?) (saved-cont continuation?))
  (throw-exp2-cont (val1 expval?) (saved-cont continuation?))
  )

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
      (let-exp-cont (var body saved-env saved-cont)
                    (value-of/k body (extend-env var val saved-env) saved-cont))
      (if-test-cont (exp2 exp3 saved-env saved-cont)
                    (if (expval->bool val)
                        (value-of/k exp2 saved-env saved-cont)
                        (value-of/k exp3 saved-env saved-cont)))
      (diff1-cont (exp2 env saved-cont)
                  (value-of/k exp2 env (diff2-cont val saved-cont)))
      (diff2-cont (val1 saved-cont)
                  (let ([num1 (expval->num val1)] [num2 (expval->num val)])
                    (apply-cont saved-cont (num-val (- num1 num2)))))
      (rator-cont
       (rands env saved-cont)
       (if (null? rands)
           (apply-procedure/k val '() saved-cont)
           (value-of/k (car rands)
                       env
                       (rands-cont val (cdr rands) '() env saved-cont))))
      (rands-cont
       (p rands vals env saved-cont)
       (let ([new-vals (cons val vals)])
         (if (null? rands)
             (apply-procedure/k p (reverse new-vals) saved-cont)
             (value-of/k (car rands)
                         env
                         (rands-cont p (cdr rands) new-vals env saved-cont)))))
      (cons-fst-cont (snd-exp env saved-cont)
                     (value-of/k snd-exp env (cons-snd-cont val saved-cont)))
      (cons-snd-cont (val1 saved-cont)
                     (apply-cont saved-cont (pair-val val1 val)))
      (car-cont (saved-cont)
                (let ([fst (expval->pair-fst val)]) (apply-cont saved-cont fst)))
      (cdr-cont (saved-cont)
                (let ([fst (expval->pair-snd val)]) (apply-cont saved-cont fst)))
      (null?-cont (saved-cont) (apply-cont saved-cont (bool-val (nil? val))))
      (list-cont
       (exps vals env saved-cont)
       (if (null? exps)
           (apply-cont saved-cont (list->pair-vals (reverse (cons val vals))))
           (value-of/k (car exps)
                       env
                       (list-cont (cdr exps) (cons val vals) env saved-cont))))
      (try-cont (var1 var2 handler-exp env saved-cont)
                (apply-cont saved-cont val))
      (raise1-cont (saved-cont) (apply-handler val saved-cont saved-cont))
      (call-cont-cont (rator saved-cont) (apply-cont rator val))
      (throw-exp1-cont (exp2 env saved-cont) (value-of/k exp2 env (throw-exp2-cont val saved-cont)))
      (throw-exp2-cont (val1 saved-cont) (apply-cont (expval->cont val) val1))

      )))

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
      (try-exp (exp1 var1 var2 handler-exp)
               (value-of/k exp1 env (try-cont var1 var2 handler-exp env cont)))
      (raise-exp (exp1) (value-of/k exp1 env (raise1-cont cont)))
      (call-cont-exp
       (var expr)
       (value-of/k expr
                   env
                   (call-cont-cont (expval->cont (apply-env env var)) cont)))
      (letcc-exp (var body)
                 ;  (display cont) (newline)
                 (value-of/k body (extend-env var (cont-val cont) env) cont))
      (throw-exp (exp1 exp2) (value-of/k exp1 env (throw-exp1-cont exp2 env cont)))
      )))

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
                      catch (x, k) -1
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
                      catch (x, k) -1
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
   in let bar = proc(dummy) try (foo 0) catch(e, k) raise -2
      in let baz = proc(dummy) try (bar 0) catch(e, k) raise -3
         in try (baz 0) catch(e, k) e")
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
  catch (e, k) e
  ")
(check-equal? (run code8) (num-val 114))

(define code9
  "
  try let x = raise 114
      in -(x, 514)
  catch (e, k) (call-cont k 114514)
  ")
(check-equal? (run code9) (num-val 114000))

(define code10
  "
  try let x = raise 114
      in -(x, 514)
  catch (e, k) (call-cont k raise -1)
  ")
(run code10)


(define code11
  "
  let x = 114
  in -(114514,
       letcc y
       in let f = proc(z) -(z, 514)
          in throw (f x) to y)
  ")
(check-equal? (run code11) (num-val 114914))


(define code12
  "
  let x = 114
  in -(114514,
       letcc y
       in let f = proc(z) -(z, 514)
          in (y (f x)))
  ")
(check-equal? (run code12) (num-val 114914))