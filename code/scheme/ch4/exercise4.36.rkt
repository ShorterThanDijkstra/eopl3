#lang eopl
(require rackunit)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Procedure data type
; procedure : Var × Exp × Env → Proc
(define-datatype
  proc
  proc?
  (procedure (var identifier?)
             (body expression?)
             (saved-env environment?)))

; apply-procedure : Proc × ExpVal → ExpVal
(define apply-procedure
  (lambda (proc1 val)
    (cases proc proc1
      (procedure (var body saved-env)
                 (value-of body
                           (extend-env var val saved-env))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Array
(define array?
  (lambda (v)
    (reference? v)))

(define make-array
  (lambda (len init-val)
    (let ((head (newref init-val)))
      (let loop ((cnt (- len 1)))
        (if (= cnt 0)
            head
            (begin
              (newref init-val)
              (loop (- cnt 1))))))))

(define array-ref
  (lambda (arr index)
    (+ arr index)))

(define array-set
  (lambda (arr index val)
    (setref! (+ arr index) val)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal data type
(define-datatype expval
  expval?
  (num-val (value number?))
  (bool-val (boolean boolean?))
  (array-val (arr array?))
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


(define expval->array
  (lambda (v)
    (cases expval v
      (array-val (val) val)
      (else (eopl:error 'expval->array "~s" v)))))
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
  (extend-env-rec (p-names (list-of identifier?))
                  (b-vars (list-of identifier?))
                  (bodys (list-of expression?))
                  (env environment?)))

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
  (let-exp (var identifier?)
           (exp expression?)
           (body expression?))
  (letrec-exp (p-names (list-of identifier?))
              (b-vars (list-of identifier?))
              (p-bodies (list-of expression?))
              (letrec-body expression?))
  (proc-exp (var identifier?) (body expression?))
  (call-exp (rator expression?) (rand expression?))
  (assign-exp (var identifier?) (exp1 expression?))
  (seq-exp (exps (list-of expression?)))
  (newarr-exp (len expression?) (init-val expression?))
  (arrref-exp (arr expression?) (index expression?))
  (arrset-exp (arr expression?) (index expression?) (val expression?))
  )

(define-datatype program
  program?
  (a-program (exp1 expression?)))

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
    (expression ("let" identifier
                       "="
                       expression
                       "in"
                       expression)
                let-exp)
    (expression ("letrec" (arbno identifier
                                 "("
                                 identifier
                                 ")"
                                 "="
                                 expression)
                          "in"
                          expression)
                letrec-exp)
    (expression
     ("proc" "(" identifier ")" expression)
     proc-exp)
    (expression ("(" expression expression ")")
                call-exp)
    (expression ("set" identifier "=" expression)
                assign-exp)
    (expression
     ("begin" (separated-list expression ";")
              "end")
     seq-exp)
    (expression
     ("newarray" "(" expression "," expression ")")
     newarr-exp)
    (expression
     ("arrayref" "(" expression "," expression ")")
     arrref-exp)
    (expression
     ("arrayset" "(" expression "," expression "," expression ")")
     arrset-exp)
    ))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec
                             the-grammar-spec))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter
; value-of-operand : Exp × Env → Ref
(define value-of-operand
  (lambda (exp env)
    (cases expression exp
      (var-exp (var) (apply-env env var))
      (arrref-exp (arr-exp index-exp)
                  (let ([arr (expval->array (value-of arr-exp env))]
                        [index (expval->num (value-of index-exp env))])
                    (array-ref arr index)))
      (else
       (newref (value-of exp env))))))

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
       (var exp1 body)
       (let ([val1 (value-of exp1 env)])
         (value-of
          body
          (extend-env var (newref val1) env))))
      (letrec-exp (proc-names bound-vars
                              proc-bodies
                              letrec-body)
                  (value-of letrec-body
                            (extend-env-rec
                             proc-names
                             bound-vars
                             proc-bodies
                             env)))
      (proc-exp
       (var body)
       (proc-val (procedure var body env)))
      (call-exp (rator rand)
                (let ((proc (expval->proc (value-of rator env)))
                      (arg (value-of-operand rand env)))
                  (apply-procedure proc arg)))
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
                                 env))))))
      (newarr-exp (len-exp init-val-exp)
                  (let ((len (expval->num (value-of len-exp env)))
                        (init-val (value-of init-val-exp env)))
                    (array-val (make-array len init-val))))
      (arrref-exp (arr-exp index-exp)
                  (let ((arr (expval->array (value-of arr-exp env)))
                        (index (expval->num (value-of index-exp env))))
                    (deref(array-ref arr index))))
      (arrset-exp (arr-exp index-exp val-exp)
                  (let ((arr (expval->array (value-of arr-exp env)))
                        (index (expval->num (value-of index-exp env)))
                        (val (value-of val-exp env)))
                    (begin
                      (array-set arr index val)
                      (num-val 73))))
      )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;run

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
(define str0
  "let p = proc (x) set x = 4
    in let a = 3
       in begin (p a); a end")
(check-equal? (run str0) (num-val 4))

(define str1
  "let f = proc (x) set x = 44
   in let g = proc (y) (f y)
      in let z = 55
         in begin (g z); z end")
(check-equal? (run str1) (num-val 44))

(define str2
  "let swap = proc (x) proc (y)
                let temp = x
                 in begin
                   set x = y;
                   set y = temp
                 end
   in let a = 33
      in let b = 44
         in begin
           ((swap a) b);
           -(a,b)
         end")
(check-equal? (run str2) (num-val 11))

(define str3
  "let b = 3
   in let p = proc (x) proc(y)
                begin
                  set x = 4;
                  y
                end
   in ((p b) b)")
(check-equal? (run str3) (num-val 4))

(define str4
  "let a = newarray(2,-99)
    in let p = proc (x)
                 let v = arrayref(x,1)
                 in arrayset(x,1,-(v,-1))
        in begin arrayset(a,1,0); (p a); (p a); arrayref(a,1) end")
(check-equal? (run str4) (num-val 2))

(define str5
  "let swap = proc (x) proc (y)
                let temp = x
                 in begin
                   set x = y;
                   set y = temp
                 end
   in let arr = newarray(2, 0)
      in begin arrayset(arr, 1, -1);
               arrayset(arr, 0, 1);
               ((swap arrayref(arr, 0)) arrayref(arr, 1));
               -(arrayref(arr, 0), arrayref(arr, 1))
        end
   ")
(check-equal? (run str5) (num-val -2))

; ((swap (arrayref a (arrayref a i))) (arrayref a j))
; => swap a of index (arrayref a i) and j
