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
       (if (not (= (length vars) (length vals)))
           (eopl:error "procedure arity mismatch")
           (value-of
            body
            (extend-env-vars
             vars
             (map (lambda (val) (newref val)) vals)
             saved-env)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal data type
(define-datatype expval
  expval?
  (num-val (value number?))
  (bool-val (boolean boolean?))
  (proc-val (proc proc?)))

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

(define the-store 'uninitialized)

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
  (extend-env-rec
   (p-names (list-of identifier?))
   (b-varss (list-of (list-of identifier?)))
   (bodys (list-of expression?))
   (proc-refs-vec vector?)
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
       (bvar bval saved-env)
       (if (eqv? search-var bvar)
           bval
           (apply-env saved-env search-var)))
      (extend-env-rec
       (p-names b-varss
                p-bodies
                proc-refs-vec
                saved-env)
       (let ([n (location search-var p-names)])
         (if n
             (if (vector-ref proc-refs-vec
                             n) ; not first call
                 (vector-ref proc-refs-vec n)
                 (let ([proc-ref
                        (begin
                          (write "call procedure: ")
                          (write (list-ref p-names n))
                          (newline)
                          (newref
                           (proc-val
                            (procedure
                             (list-ref b-varss n)
                             (list-ref p-bodies n)
                             env))))])
                   (begin
                     (vector-set! proc-refs-vec
                                  n
                                  proc-ref)
                     proc-ref)))

             (apply-env saved-env search-var)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Expression data type && Program
(define identifier?
  (lambda (exp)
    (and (symbol? exp) (not (eqv? exp 'lambda)))))

(define-datatype
  expression
  expression?
  (const-exp (num number?))
  (if-exp (exp1 expression?)
          (exp2 expression?)
          (exp3 expression?))
  (zero?-exp (exp1 expression?))
  (var-exp (var identifier?))
  (diff-exp (exp1 expression?) (exp2 expression?))
  (let-exp (vars (list-of identifier?))
           (exps (list-of expression?))
           (body expression?))
  (letrec-exp
   (p-names (list-of identifier?))
   (b-varss (list-of (list-of identifier?)))
   (p-bodies (list-of expression?))
   (letrec-body expression?))
  (proc-exp (vars (list-of identifier?))
            (body expression?))
  (call-exp (rator expression?)
            (rands (list-of expression?)))
  (assign-exp (var identifier?) (exp1 expression?))
  (seq-exp (exps (list-of expression?))))

(define-datatype program
  program?
  (a-program (exp1 expression?)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter

; value-of : Exp × Env → ExpVal
(define value-of
  (lambda (exp env)
    (cases
        expression
      exp
      (const-exp (num) (num-val num))
      (var-exp (var) (deref (apply-env env var)))
      (diff-exp (exp1 exp2)
                (let ([val1 (value-of exp1 env)]
                      [val2 (value-of exp2 env)])
                  (let ([num1 (expval->num val1)]
                        [num2 (expval->num val2)])
                    (num-val (- num1 num2)))))
      (if-exp (exp1 exp2 exp3)
              (let ([val1 (value-of exp1 env)])
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      (zero?-exp (exp1)
                 (let ([val1 (value-of exp1 env)])
                   (let ([num1 (expval->num val1)])
                     (if (zero? num1)
                         (bool-val #t)
                         (bool-val #f)))))
      (let-exp
       (vars exps body)
       (let ([vals (map (lambda (expr)
                          (value-of expr env))
                        exps)])
         (value-of
          body
          (extend-env-vars
           vars
           (map (lambda (val) (newref val)) vals)
           env))))
      (letrec-exp
       (proc-names bound-varss
                   proc-bodies
                   letrec-body)
       (value-of
        letrec-body
        (extend-env-rec
         proc-names
         bound-varss
         proc-bodies
         (make-vector (length proc-names) #f)
         env)))
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
         (apply-procedure proc args)))
      (assign-exp (var exp1)
                  (begin
                    (setref! (apply-env env var)
                             (value-of exp1 env))
                    (num-val 27)))
      (seq-exp
       (exps)
       (if (null? exps)
           (eopl:error 'value-of " empty seq-exp")
           (let loop ([rest (cdr exps)]
                      [last-val
                       (value-of (car exps) env)])
             (if (null? rest)
                 last-val
                 (loop (cdr rest)
                       (value-of (car rest)
                                 env)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;run
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
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression (identifier) var-exp)
    (expression
     ("-" "(" expression "," expression ")")
     diff-exp)
    (expression ("zero?" "(" expression ")")
                zero?-exp)
    (expression ("if" expression
                      "then"
                      expression
                      "else"
                      expression)
                if-exp)
    (expression
     ("let" (arbno identifier "=" expression)
            "in"
            expression)
     let-exp)
    (expression
     ("letrec" (arbno identifier
                      "("
                      (arbno identifier)
                      ")"
                      "="
                      expression)
               "in"
               expression)
     letrec-exp)
    (expression ("proc" "("
                        (arbno identifier)
                        ")"
                        expression)
                proc-exp)
    (expression
     ("(" expression (arbno expression) ")")
     call-exp)
    (expression ("set" identifier "=" expression)
                assign-exp)
    (expression
     ("begin" (separated-list expression ";")
              "end")
     seq-exp)))

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
       (exp1)
       (value-of exp1 (init-env))))))

(define run
  (lambda (str)
    (value-of-program (scan&parse str))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;test
(define str1
  "let x = 0
   in letrec even(dummy) = if zero?(x)
                              then true
                              else begin
                                    set x = -(x, 1);
                                    (odd 888)
                                   end
             odd(dummy) = if zero?(x)
                             then false
                             else begin
                                 set x = -(x, 1);
                                 (even 888)
                             end
      in begin
          set x = 13;
          (odd -888)
         end")
(check-equal? (run str1) (bool-val #t))

(define str2
  "let g = let counter = 0
           in proc (dummy)
                begin
                  set counter = -(counter, -1);
                  counter
                end
  in let a = (g 11)
     in let b = (g 11)
        in -(a,b)")
(check-equal? (run str2) (num-val -1))

(define str3
  "
  letrec
    even(x) = if zero?(x) then true else (odd -(x,1))
    odd(x) = if zero?(x) then false else (even -(x,1))
  in (odd 14)
")
(check-equal? (run str3) (bool-val #f))

(define str4
  "let f = proc (x) proc (y)
            begin
              set x = -(x,-1);
              -(x,y)
            end
  in ((f 44) 33)")
(check-equal? (run str4) (num-val 12))

(define str5
  "let sum = 0
   in begin
        set sum = proc (x y z)
                   -(x, -(0, -(y, -(0, z))));
        (sum 11 45 14)
      end")
(check-equal? (run str5) (num-val 70))

(define str6
  "let add2 = proc (x y) -(x, -(0, y))
       add3 = proc (x y z) -(x, -(0, -(y, -(0, z))))
   in (add2 (add3 1 2 3) (add3 4 5 6))
  ")
(check-equal? (run str6) (num-val 21))
