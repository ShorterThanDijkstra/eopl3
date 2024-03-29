#lang eopl
(require rackunit)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Procedure data type
; procedure : Var × Exp × Env → Proc
(define-datatype proc proc?
  (procedure
   (var identifier?)
   (body expression?)
   (saved-env environment?)))
; apply-procedure : Proc × ExpVal → ExpVal
(define apply-procedure
  (lambda (proc1 val)
    (cases proc proc1
      (procedure (var body saved-env)
                 (value-of body (extend-env var val saved-env))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal data type
(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val (proc proc?))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal -> scheme value

(define expval->num
  (lambda (v debug)
    (cases expval v
      	(num-val (num) num)
      	(else (eopl:error 'expval->num "~s" debug)))))

(define expval->bool
  (lambda (v)
    (cases expval v
      	(bool-val (bool) bool)
      	(else (eopl:error 'expval->bool "~s" v)))))

(define expval->proc
  (lambda (v)
    (cases expval v
      	(proc-val (proc) proc)
      	(else (eopl:error 'expval->proc "~s" v)))))

(define expval->scheme-val
  (lambda (v)
    (cases expval v
      (num-val (num) num)
      (bool-val (bool) bool)
      (proc-val (proc) proc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Env
(define empty-env-record
  (lambda ()
    '()))

(define extended-env-record
  (lambda (sym val old-env)
    (cons (list sym val) old-env)))

(define empty-env-record? null?)

(define environment?
  (lambda (x)
    (or (empty-env-record? x)
        (and (pair? x)
             (symbol? (car (car x)))
             (expval? (cadr (car x)))
             (environment? (cdr x))))))

(define extended-env-record->sym
  (lambda (r)
    (car (car r))))

(define extended-env-record->val
  (lambda (r)
    (cadr (car r))))

(define extended-env-record->old-env
  (lambda (r)
    (cdr r)))

(define empty-env
  (lambda ()
    (empty-env-record)))

(define empty-env?
  (lambda (x)
    (empty-env-record? x)))

(define extend-env
  (lambda (sym val old-env)
    (extended-env-record sym val old-env)))

(define extend-env-list
  (lambda (syms vals old-env)
    (if (null? syms)
        old-env
        (extend-env-list (cdr syms) (cdr vals)
                         (extend-env (car syms) (car vals) old-env)))))

(define apply-env
  (lambda (env search-sym)
    (if (empty-env? env)
        (eopl:error 'apply-env "No binding for ~s" search-sym)
        	(let ((sym (extended-env-record->sym env))
                      (val (extended-env-record->val env))
                      (old-env (extended-env-record->old-env env)))
                  (if (eqv? search-sym sym)
                      val
                      (apply-env old-env search-sym))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Expression data type
(define identifier?
  (lambda (exp)
    (and (symbol? exp)
         (not (eqv? exp 'lambda)))))

(define-datatype expression expression?
  (const-exp
   (num number?))
  (if-exp
   (exp1 expression?)
   (exp2 expression?)
   (exp3 expression?))
  (zero?-exp
   (exp expression?))
  (var-exp
   (var identifier?))
  (diff-exp
   (exp1 expression?)
   (exp2 expression?))
  (let-exp
   (var  identifier?)
   (exp  expression?)
   (body expression?))
  (proc-exp
   (var identifier?)
   (body expression?))
  (call-exp
   (rator expression?)
   (rand expression?))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter

(define init-env
  (lambda ()
    (extend-env
     'i (num-val 1)
     (extend-env
      'v (num-val 5)
      (extend-env
       'x (num-val 10)
       (empty-env))))))

; value-of : Exp × Env → ExpVal
(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (var-exp (var) (apply-env env var))
      (diff-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1 'diff-exp))
                        (num2 (expval->num val2 'diff-exp)))
                    (num-val
                     (- num1 num2)))))
      (zero?-exp (exp1)
                 (let ((val1 (value-of exp1 env)))
                   (let ((num1 (expval->num val1 'zero?-exp)))
                     (if (zero? num1)
                         (bool-val #t)
                         (bool-val #f)))))
      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 env)))
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      (let-exp (var exp body)
               (value-of body
                         (extend-env var (value-of exp env) env)))
      (proc-exp (var body)
                (proc-val (procedure var body env)))
      (call-exp (rator rand)
                (let ((proc (expval->proc (value-of rator env)))
                      (arg (value-of rand env)))
                  (apply-procedure proc arg)))
      )))

; let makemult = proc (maker)
;                 proc (x)
;                  if zero?(x)
;                  then 0
;                  else -(((maker maker) -(x,1)), -4)
; in let times4 = proc (x) ((makemult makemult) x)
;    in (times4 3)

; (times 3)
; ((makemult makemult) 3)
; (<proc> 3)
; -(((makemult makemult) 2), -4)
; -((<proc> 2), 4)
; -(-(((makemult makemult) 1), -4), 4)
; -(-((<proc> 1), -4), 4)
; -(-(-(((maker maker) 0), -4), -4), 4)
; -(-(-((<proc> 0), -4), -4), 4)
; -(-(-(0, -4), -4), 4)
; 12

; let make-mult = proc (maker)
;                 proc (x)
;                  proc (y)
;                   if zero?(y)
;                   then 0
;                   else -((((maker maker) -(y,1)) x), -(0, x))
; in let times = (make-mult make-mult)
;    in let make-factorial = proc (maker)
;                              proc (n)
;                                if zero?(n)
;                                   then 1
;                                   else ((times n) ((maker maker) -(n , 1)))
;       in let factorial = (make-factorial make-factorial)
;          in (factorial 10)

(define ast
  (let-exp 'make-mult
           (proc-exp 'maker
                     (proc-exp 'x
                               (proc-exp 'y
                                         (if-exp (zero?-exp (var-exp 'y))
                                                 (const-exp 0)
                                                 (diff-exp (call-exp (call-exp (call-exp (var-exp 'maker) (var-exp 'maker))
                                                                               (diff-exp (var-exp 'y) (const-exp 1)))
                                                                     (var-exp 'x))
                                                           (diff-exp (const-exp 0)
                                                                     (var-exp 'x)))))))
           (let-exp 'times
                    (call-exp (var-exp 'make-mult) (var-exp 'make-mult))
                    (let-exp 'make-factorial
                             (proc-exp 'maker
                                       (proc-exp 'n
                                        (if-exp (zero?-exp (var-exp 'n))
                                                (const-exp 1)
                                                (call-exp (call-exp (var-exp 'times) (var-exp 'n))
                                                          (call-exp (call-exp (var-exp 'maker) (var-exp 'maker))
                                                                    (diff-exp (var-exp 'n)
                                                                              (const-exp 1)))))))
                             (let-exp 'factorial
                                      (call-exp (var-exp 'make-factorial) (var-exp 'make-factorial))
                                      (call-exp (var-exp 'factorial) (const-exp 10)))))))
(check-equal? (value-of ast (init-env)) (num-val 3628800))