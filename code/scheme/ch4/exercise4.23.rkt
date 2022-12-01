#lang eopl
(require rackunit)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Procedure data type
; procedure : Var × Exp × Env → Proc
(define-datatype
  proc
  proc?
  (procedure (vars (list-of identifier?))
             (body expression?)
             (saved-env environment?)))
; apply-procedure : Proc × ExpVal → ExpVal
(define apply-procedure
  (lambda (proc1 vals)
    (cases
        proc
      proc1
      (procedure
       (vars body saved-env)
       (value-of
        body
        (extend-env-vars
         vars
         (map (lambda (val) (newref val)) vals)
         saved-env))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal data type
(define-datatype expval
  expval?
  (num-val (value number?))
  (bool-val (boolean boolean?))
  (proc-val (proc proc?)))

(define expval->val
  (lambda (v)
    (cases expval
      v
      (num-val (num) num)
      (bool-val (bool) bool)
      (proc-val (proc) proc))))

(define expval->num
  (lambda (v)
    (cases
        expval
      v
      (num-val (num) num)
      (else (eopl:error 'expval->num "~s" v)))))

(define expval->bool
  (lambda (v)
    (cases
        expval
      v
      (bool-val (bool) bool)
      (else (eopl:error 'expval->bool "~s" v)))))

(define expval->proc
  (lambda (v)
    (cases
        expval
      v
      (proc-val (proc) proc)
      (else (eopl:error 'expval->proc "~s" v)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Store
; empty-store : () → Sto
(define empty-store (lambda () '()))
; usage: A Scheme variable containing the current state
; of the store. Initially set to a dummy value.
(define uninitialized 'uninitialized)

(define the-store uninitialized)

; get-store : () → Sto
(define get-store (lambda () the-store))

; initialize-store! : () → Unspecified
; usage: (initialize-store!) sets the-store to the empty store
(define initialize-store!
  (lambda () (set! the-store (empty-store))))

; reference? : SchemeVal → Bool
(define reference? (lambda (v) (integer? v)))

; newref : ExpVal → Ref
(define newref
  (lambda (val)
    (let ([next-ref (length the-store)])
      (set! the-store
            (append the-store (list val)))
      next-ref)))

; deref : Ref → ExpVal
(define deref
  (lambda (ref) (list-ref the-store ref)))

; setref! : Ref × ExpVal → Unspecified
; usage: sets the-store to a state like the original, but with
; position ref containing val.
(define setref!
  (lambda (ref val)
    (set!
     the-store
     (letrec
         ([setref-inner
           ; usage: returns a list like store1, except that
           ; position ref1 contains val.
           (lambda (store1 ref1)
             (cond
               [(null? store1)
                (eopl:error
                 "report-invalid-reference ~s"
                 ref
                 the-store)]
               [(zero? ref1)
                (cons val (cdr store1))]
               [else
                (cons (car store1)
                      (setref-inner
                       (cdr store1)
                       (- ref1 1)))]))])
       (setref-inner the-store ref)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Env
(define-datatype
  environment
  environment?
  (empty-env)
  (extend-env (var identifier?)
              (ref reference?)
              (env environment?))
  (extend-env-rec (p-names (list-of identifier?))
                  (b-vars (list-of identifier?))
                  (bodys (list-of expression?))
                  (env environment?)))

(define extend-env-vars
  (lambda (vars refs saved-env)
    (if (null? vars)
        saved-env
        (extend-env (car vars)
                    (car refs)
                    (extend-env-vars
                     (cdr vars)
                     (cdr refs)
                     saved-env)))))
(define location
  (lambda (search names)
    (let loop ([pos 0] [names names])
      (cond
        [(null? names) #f]
        [(eqv? (car names) search) pos]
        [else (loop (+ pos 1) (cdr names))]))))

(define apply-env
  (lambda (env search-var)
    (cases
        environment
      env
      (empty-env ()
                 (eopl:error 'apply-env
                             "No binding for ~s"
                             search-var))
      (extend-env
       (bvar ref saved-env)
       (if (eqv? search-var bvar)
           ref
           (apply-env saved-env search-var)))
      (extend-env-rec
       (p-names b-vars p-bodies saved-env)
       (let ([n (location search-var p-names)])
         (if n
             (newref (proc-val
                      (procedure
                       (list-ref b-vars n)
                       (list-ref p-bodies n)
                       env)))
             (apply-env saved-env search-var)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Paring && Expression && Statement
(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter
      (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define the-grammar-spec
  '((program (statement) a-program)
    (expression (number) const-exp)
    (expression ("not" "(" expression ")")
                not-exp)
    (expression (identifier) var-exp)
    (expression
     ("-" "(" expression "," expression ")")
     diff-exp)
    (expression
     ("+" "(" expression "," expression ")")
     add-exp)
    (expression
     ("*" "(" expression "," expression ")")
     mul-exp)
    (expression ("zero?" "(" expression ")")
                zero?-exp)
    (expression
     ("proc" "("
             (separated-list identifier ",")
             ")"
             expression)
     proc-exp)
    (expression
     ("(" expression (arbno expression) ")")
     call-exp)
    (statement (identifier "=" expression)
               assign-stmt)
    (statement ("print" expression) print-stmt)
    (statement ("read" identifier) read-stmt)

    (statement
     ("{" (separated-list statement ";") "}")
     seq-stmt)
    (statement
     ("if" expression statement statement)
     if-stmt)
    (statement ("while" expression statement)
               while-stmt)
    (statement
     ("var" (separated-list identifier ",")
            ";"
            statement)
     block-stmt)))
(define identifier?
  (lambda (exp)
    (and (symbol? exp) (not (eqv? exp 'lambda)))))

(define-datatype
  expression
  expression?
  (const-exp (expr number?))
  (var-exp (expr identifier?))
  (not-exp (expr expression?))
  (diff-exp (expr1 expression?)
            (expr2 expression?))
  (add-exp (expr1 expression?) (expr2 expression?))
  (mul-exp (expr1 expression?) (expr2 expression?))
  (zero?-exp (expr1 expression?))
  (proc-exp (vars (list-of identifier?))
            (body expression?))
  (call-exp (rantor expression?)
            (rands (list-of expression?))))

(define-datatype
  statement
  statement?
  (assign-stmt (var identifier?)
               (expr expression?))
  (print-stmt (expr expression?))
  (read-stmt (var identifier?))
  (seq-stmt (stmts (list-of statement?)))
  (if-stmt (pred expression?)
           (conseq statement?)
           (alter statement?))
  (while-stmt (pred expression?) (stmt statement?))
  (block-stmt (vars (list-of identifier?))
              (stmt statement?)))

(define-datatype program
  program?
  (a-program (stmt statement?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter

; value-of : Exp × Env → ExpVal
(define value-of
  (lambda (exp env)
    (cases
        expression
      exp
      (const-exp (num) (num-val num))
      (var-exp
       (var)
       (let ([val (deref (apply-env env var))])
         (if (eqv? val uninitialized)
             (eopl:error
              'var-exp
              "Variable is not initialized: ~s"
              var)
             val)))
      (not-exp (expr)
               (if (expval->bool
                    (value-of expr env))
                   (bool-val #f)
                   (bool-val #t)))
      (diff-exp (exp1 exp2)
                (let ([val1 (value-of exp1 env)]
                      [val2 (value-of exp2 env)])
                  (let ([num1 (expval->num val1)]
                        [num2 (expval->num val2)])
                    (num-val (- num1 num2)))))
      (mul-exp (exp1 exp2)
               (let ([val1 (value-of exp1 env)]
                     [val2 (value-of exp2 env)])
                 (let ([num1 (expval->num val1)]
                       [num2 (expval->num val2)])
                   (num-val (* num1 num2)))))
      (add-exp (exp1 exp2)
               (let ([val1 (value-of exp1 env)]
                     [val2 (value-of exp2 env)])
                 (let ([num1 (expval->num val1)]
                       [num2 (expval->num val2)])
                   (num-val (+ num1 num2)))))
      (zero?-exp (exp1)
                 (let ([val1 (value-of exp1 env)])
                   (let ([num1 (expval->num val1)])
                     (if (zero? num1)
                         (bool-val #t)
                         (bool-val #f)))))
      (proc-exp
       (vars body)
       (proc-val (procedure vars body env)))
      (call-exp
       (rator rands)
       (let ([proc (expval->proc
                    (value-of rator env))]
             [args (map (lambda (rand)
                          (value-of rand env))
                        rands)])
         (apply-procedure proc args))))))

(define result-of
  (lambda (stmt env)
    (cases
        statement
      stmt
      (assign-stmt (var expr)
                   (setref! (apply-env env var)
                            (value-of expr env)))
      (print-stmt
       (expr)
       (let ([val (expval->val
                   (value-of expr env))])
         (if (proc? val)
             (write "<procedure>")
             (write val))
         (newline)))
      (read-stmt (var)
                 (let ((input (read)))
                   (if (number? input)
                       (setref! (apply-env env var) (num-val input))
                       (eopl:error "Please enter a number"))))
      (seq-stmt (stmts)
                (let loop ([stmts stmts])
                  (if (null? stmts)
                      '()
                      (begin
                        (result-of (car stmts) env)
                        (loop (cdr stmts))))))
      (if-stmt (pred conseq alter)
               (if (expval->bool
                    (value-of pred env))
                   (result-of conseq env)
                   (result-of alter env)))
      (while-stmt (pred stmt)
                  (let loop ()
                    (if (expval->bool
                         (value-of pred env))
                        (begin
                          (result-of stmt env)
                          (loop))
                        '())))
      (block-stmt
       (vars stmt)
       (let loop ([vars vars] [env env])
         (if (null? vars)
             (result-of stmt env)
             (let ([new-env (extend-env
                             (car vars)
                             (newref uninitialized)
                             env)])
               (loop (cdr vars) new-env))))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;run

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec
                             the-grammar-spec))

(define init-env
  (lambda ()
    (extend-env 'true
                (newref (bool-val #t))
                (extend-env 'false
                            (newref (bool-val #f))
                            (empty-env)))))

; value-of-program : Program → ExpVal
(define value-of-program
  (lambda (pgm)
    (initialize-store!)
    (cases program
      pgm
      (a-program
       (stmt)
       (result-of stmt (init-env))))))

(define run
  (lambda (str)
    (value-of-program (scan&parse str))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;test
(define str1
  "var x,y; {x = 3; y = 4; print +(x,y)}")

(define str2
  "var x,y,z;
   {x = 3;
    y = 9;
    z = 0;
    while not(zero?(x))
      {z = +(z,y); x = -(x,1)};
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

(define str6
  "var f; {f = proc(x,y) *(x,y); print f}")

(define str7 "print foo")

(define str8 "var foo; {read foo; print foo}")

(run str1)
(run str2)
(run str3)
(run str4)
(run str6)
(run str8)

; (run str5) ;should threw an error
; (run str7) ;should threw an error
