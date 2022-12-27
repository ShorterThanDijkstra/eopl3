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

(define show-expval
  (lambda (v)
    (cases expval
           v
           (num-val (num) num)
           (bool-val (bool) bool)
           (proc-val (proc) "<procedure>")
           (pair-val (fst snd) "<pair>")
           (nil-val () "nil"))))
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
; Store
(define empty-store (lambda () '()))

(define the-store 'uninitialized)

(define get-store (lambda () the-store))

(define initialize-store! (lambda () (set! the-store (empty-store))))

(define reference? (lambda (v) (integer? v)))

(define newref
  (lambda (val)
    (let ([next-ref (length the-store)])
      (set! the-store (append the-store (list val)))
      next-ref)))

(define deref (lambda (ref) (list-ref the-store ref)))

(define setref!
  (lambda (ref val)
    (set!
     the-store
     (letrec ([setref-inner
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
                 (b-vars (list-of identifier?))
                 (p-body expression?)
                 (env environment?)))

(define extend-env-vars
  (lambda (vars vals env)
    (if (null? vars)
        env
        (extend-env (car vars)
                    (newref (car vals))
                    (extend-env-vars (cdr vars) (cdr vals) env)))))
(define apply-env
  (lambda (env search-var)
    (cases environment
           env
           (empty-env () (eopl:error 'apply-env "No binding for ~s" search-var))
           (extend-env
            (bvar ref saved-env)
            (if (eqv? search-var bvar) ref (apply-env saved-env search-var)))
           (extend-env-rec (p-name b-vars p-body saved-env)
                           (if (eqv? p-name search-var)
                               (newref (proc-val (procedure b-vars p-body env)))
                               (apply-env saved-env search-var))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Expression && Parsing
(define identifier? (lambda (exp) (and (symbol? exp) (not (eqv? exp 'lambda)))))

(define-datatype program program? (a-program (stmt statement?)))

(define-datatype
 statement
 statement?
 (assign-stmt (var identifier?) (expr expression?))
 (print-stmt (expr expression?))
 (seq-stmt (stmts (list-of statement?)))
 (if-stmt (pred expression?) (conseq statement?) (alter statement?))
 (while-stmt (pred expression?) (stmt statement?))
 (block-stmt (vars (list-of identifier?)) (stmt statement?)))

(define-datatype
 expression
 expression?
 (const-exp (num number?))
 (if-exp (exp1 expression?) (exp2 expression?) (exp3 expression?))
 (zero?-exp (exp1 expression?))
 (not-exp (exp1 expression?))
 (var-exp (var identifier?))
 (diff-exp (exp1 expression?) (exp2 expression?))
 (add-exp (exp1 expression?) (exp2 expression?))
 (mul-exp (exp1 expression?) (exp2 expression?))
 (let-exp (vars (list-of identifier?))
          (exps (list-of expression?))
          (body expression?))
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
 (list-exp (exps (list-of expression?))))

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define the-grammar-spec
  '((program (statement) a-program)
    (expression (number) const-exp)
    (expression (identifier) var-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("+" "(" expression "," expression ")") add-exp)
    (expression ("*" "(" expression "," expression ")") mul-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("not" "(" expression ")") not-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression)
                let-exp)
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
    (statement (identifier "=" expression) assign-stmt)
    (statement ("print" expression) print-stmt)
    (statement ("{" (separated-list statement ";") "}") seq-stmt)
    (statement ("if" expression statement statement) if-stmt)
    (statement ("while" expression statement) while-stmt)
    (statement ("var" (separated-list identifier ",") ";" statement)
               block-stmt)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar-spec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;Continuation
(define-datatype
 expr-cont
 expr-cont?
 (zero1-cont (cont cont?))
 (not-cont (saved-cont cont?))
 (let-exp-cont (vars (list-of identifier?))
               (exps (list-of expression?))
               (vals (list-of expval?))
               (body expression?)
               (env environment?)
               (cont cont?))
 (if-test-cont (exp2 expression?)
               (exp3 expression?)
               (env environment?)
               (cont cont?))
 (diff1-cont (exp2 expression?) (env environment?) (cont cont?))
 (diff2-cont (val1 expval?) (cont cont?))
 (add1-cont (exp2 expression?) (env environment?) (cont cont?))
 (add2-cont (val1 expval?) (cont cont?))
 (mul1-cont (exp2 expression?) (env environment?) (cont cont?))
 (mul2-cont (val1 expval?) (cont cont?))
 (rator-cont (rands (list-of expression?)) (env environment?) (cont cont?))
 (rands-cont (p expval?)
             (rands (list-of expression?))
             (vals (list-of expval?))
             (env environment?)
             (cont cont?))
 (cons-fst-cont (snd-exp expression?) (env environment?) (cont cont?))
 (cons-snd-cont (val1 expval?) (cont cont?))
 (car-cont (cont cont?))
 (cdr-cont (cont cont?))
 (null?-cont (cont cont?))
 (list-cont (exps (list-of expression?))
            (vals (list-of expval?))
            (env environment?)
            (cont cont?)))

(define apply-expr-cont
  (lambda (cont val)
    (cases
     expr-cont
     cont
     (zero1-cont (saved-cont)
                 (apply-cont saved-cont (bool-val (zero? (expval->num val)))))
     (not-cont (saved-cont)
               (apply-cont saved-cont (bool-val (not (expval->bool val)))))
     (let-exp-cont
      (vars exps vals body env saved-cont)
      (if (null? exps)
          (value-of/k body
                      (extend-env-vars vars (reverse (cons val vals)) env)
                      saved-cont)
          (value-of/k
           (car exps)
           env
           (let-exp-cont vars (cdr exps) (cons val vals) body env saved-cont))))
     (if-test-cont (exp2 exp3 saved-env saved-cont)
                   (if (expval->bool val)
                       (value-of/k exp2 saved-env saved-cont)
                       (value-of/k exp3 saved-env saved-cont)))
     (diff1-cont (exp2 env cont) (value-of/k exp2 env (diff2-cont val cont)))
     (diff2-cont (val1 cont)
                 (let ([num1 (expval->num val1)] [num2 (expval->num val)])
                   (apply-cont cont (num-val (- num1 num2)))))
     (add1-cont (exp2 env cont) (value-of/k exp2 env (add2-cont val cont)))
     (add2-cont (val1 cont)
                (let ([num1 (expval->num val1)] [num2 (expval->num val)])
                  (apply-cont cont (num-val (+ num1 num2)))))
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

(define-datatype
 command-cont
 command-cont?
 (end-cont)
 (assign-stmt-cont (var identifier?) (env environment?) (saved-cont cont?))
 (print-stmt-cont (saved-cont cont?))
 (seq-stmt-cont (stmts (list-of statement?))
                (env environment?)
                (saved-cont cont?))
 (if-stmt-cont (conseq statement?)
               (alter statement?)
               (env environment?)
               (saved-cont cont?))
 (while-pred-cont (pred expression?)
                  (stmt statement?)
                  (env environment?)
                  (saved-cont cont?))
 (while-stmt-cont (pred expression?)
                  (stmt statement?)
                  (env environment?)
                  (saved-cont cont?)))

(define apply-command-cont
  (lambda (cont val)
    (cases
     command-cont
     cont
     (end-cont ()
               (begin
                 ;(eopl:printf "End of computation:~s.~%" val)
                 val))
     (assign-stmt-cont (var env saved-cont)
                       (begin
                         (setref! (apply-env env var) val)
                         (apply-command-cont saved-cont (nil-val))))
     (print-stmt-cont (saved-cont)
                      (begin
                        (display (show-expval val))
                        (newline)
                        (apply-command-cont saved-cont (nil-val))))
     (seq-stmt-cont
      (stmts env saved-cont)
      (if (null? stmts)
          (apply-command-cont saved-cont (nil-val))
          (result-of/k (car stmts)
                       env
                       (seq-stmt-cont (cdr stmts) env saved-cont))))
     (if-stmt-cont (conseq alter env saved-cont)
                   (if (expval->bool val)
                       (result-of/k conseq env saved-cont)
                       (result-of/k alter env saved-cont)))
     (while-pred-cont
      (pred stmt env saved-cont)
      (if (expval->bool val)
          (result-of/k stmt env (while-stmt-cont pred stmt env saved-cont))
          (apply-command-cont saved-cont (nil-val))))
     (while-stmt-cont
      (pred stmt env saved-cont)
      (value-of/k pred env (while-pred-cont pred stmt env saved-cont))))))

(define cont? (lambda (cont) (or (command-cont? cont) (expr-cont? cont))))

(define apply-cont
  (lambda (cont val)
    (cond
      [(expr-cont? cont) (apply-expr-cont cont val)]
      [(command-cont? cont) (apply-command-cont cont val)]
      [else (eopl:error 'apply-cont "unknown continuation ~s.~%" cont)])))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter
(define init-env
  (lambda ()
    (extend-env 'true
                (newref (bool-val #t))
                (extend-env 'false (newref (bool-val #f)) (empty-env)))))

(define result-of-program
  (lambda (pgm)
    (initialize-store!)
    (cases program
           pgm
           (a-program (stmt) (result-of/k stmt (init-env) (end-cont))))))

(define result-of/k
  (lambda (stmt env cont)
    (cases
     statement
     stmt
     (assign-stmt (var expr)
                  (value-of/k expr env (assign-stmt-cont var env cont)))
     (print-stmt (expr) (value-of/k expr env (print-stmt-cont cont)))
     (seq-stmt
      (stmts)
      (if (null? stmts)
          (apply-command-cont cont (nil-val))
          (result-of/k (car stmts) env (seq-stmt-cont (cdr stmts) env cont))))
     (if-stmt (pred conseq alter)
              (value-of/k pred env (if-stmt-cont conseq alter env cont)))
     (while-stmt (pred stmt)
                 (value-of/k pred env (while-pred-cont pred stmt env cont)))
     (block-stmt
      (vars stmt)
      (let loop ([vars vars] [env env])
        (if (null? vars)
            (result-of/k stmt env cont)
            (loop (cdr vars)
                  (extend-env (car vars) (newref (nil-val)) env))))))))

(define value-of/k
  (lambda (exp env cont)
    (cases
     expression
     exp
     (const-exp (num) (apply-cont cont (num-val num)))
     (var-exp (var) (apply-cont cont (deref (apply-env env var))))
     (proc-exp (vars body)
               (apply-cont cont (proc-val (procedure vars body env))))
     (letrec-exp
      (p-name b-vars p-body letrec-body)
      (value-of/k letrec-body (extend-env-rec p-name b-vars p-body env) cont))
     (zero?-exp (exp1) (value-of/k exp1 env (zero1-cont cont)))
     (not-exp (exp1) (value-of/k exp1 env (not-cont cont)))
     (if-exp (exp1 exp2 exp3)
             (value-of/k exp1 env (if-test-cont exp2 exp3 env cont)))
     (let-exp (vars exps body)
              (if (null? vars)
                  (value-of/k body env cont)
                  (value-of/k
                   (car exps)
                   env
                   (let-exp-cont vars (cdr exps) '() body env cont))))
     (diff-exp (exp1 exp2) (value-of/k exp1 env (diff1-cont exp2 env cont)))
     (add-exp (exp1 exp2) (value-of/k exp1 env (add1-cont exp2 env cont)))
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
(define run (lambda (code) (result-of-program (scan&parse code))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(trace value-of/k)
(trace result-of/k)

;;;test
(define str1 "var x,y; {x = 3; y = 4; print +(x,y)}")

(define str2
  "var x,y,z;
   {x = 3;
    y = 9;
    z = 0;
    while not(zero?(x))
      { print z; z = +(z,y); x = -(x,1)};
    print z}")

(define str3
  "var x;
   {x = 3;
    print x;
    var x; {x = 5; print x};
    print x}")

(define str4
  "var f,x; {f = proc(x,y) *(x,y);
           x = 3;
           print (f 4 x)}")

(define str5 "var x; {print x}")

(define str6 "var f; {f = proc(x,y) *(x,y); print f}")

(define str7 "print foo")

(define str8 "var x, res; {
                           x = 10;
                           res = letrec fact(n, res) = if zero?(n) then res else (fact -(n, 1) *(n, res))
                                 in (fact 10 1);
                           print res}")
; (run str1)
; (run str2)
; (run str3)
; (run str4)
; (run str6)
; (run str5)
; (run str7) ;should threw an error
(run str8)
