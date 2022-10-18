#lang eopl
(require rackunit)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal data type
(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (list-val (lst list?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal -> scheme value
(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
                	variant value)))

(define expval->num
  (lambda (v)
    (cases expval v
      	(num-val (num) num)
      	(else (expval-extractor-error 'num v)))))

(define expval->bool
  (lambda (v)
    (cases expval v
      	(bool-val (bool) bool)
      	(else (expval-extractor-error 'bool v)))))

(define expval->list
  (lambda (v)
    (cases expval v
      	(list-val (lst) lst)
      	(else (expval-extractor-error 'lst v)))))

(define expval->scheme-val
  (lambda (v)
    (cases expval v
      (num-val (num) num)
      (bool-val (bool) bool)
      (list-val (lst) lst))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Scheme value -> ExpVal
(define expval-constructor-error
  (lambda (value)
    (eopl:error 'scheme-val->expval "Bad Scheme Value" value)))

(define scheme-val->expval
  (lambda (sv)
    (cond [(number? sv) (num-val sv)]
          [(boolean? sv) (bool-val sv)]
          [(list? sv) (list-val sv)]
          [else (expval-constructor-error sv)])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Env
(define init-env
  (lambda ()
    (extend-env
     'i (num-val 1)
     (extend-env
      'v (num-val 5)
      (extend-env
       'x (num-val 10)
       (empty-env))))))

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
  (var-exp
   (var identifier?))
  (let-exp
   (vars (list-of identifier?))
   (exps (list-of expression?))
   (body expression?))
   (let*-exp
   (vars (list-of identifier?))
   (exps (list-of expression?))
   (body expression?))
  (op-exp
   (op procedure?) ;;; list of ExpVal -> ExpVal
   (exps (list-of expression?)))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter
; value-of : Exp × Env → ExpVal
(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (var-exp (var) (apply-env env var))
      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 env)))
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      (let-exp (vars exps body)
               (value-of body
                         (extend-env-list vars
                                          (map (lambda (exp) (value-of exp env)) exps) env)))
      (let*-exp (vars exps body)
        (let go ([vars_ vars]
                 [exps_ exps]
                 [env_ env])
          (if (null? vars_)
              (value-of body env_)
              (go (cdr vars_) (cdr exps_) (extend-env (car vars_) (value-of (car exps_) env_) env_)))))
      (op-exp (op exps)
              (op
               (map (lambda (exp) (value-of exp env)) exps))) ;;; list of ExpVal
      )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; primitive oprations
; value-of : Exp × Env → ExpVal
(define diff-exp
  (lambda (exp1 exp2)
    (if (or (not (expression? exp1)) (not (expression? exp2)))
        (eopl:error "error")
        (op-exp
         (lambda (expvals)
           (num-val (- (expval->num (car expvals))
                       (expval->num (cadr expvals)))))
         (list exp1 exp2)))))

(define minus-exp
  (lambda (exp1)
    (if (not (expression? exp1))
        (eopl:error "error")
        (op-exp
         (lambda (expvals)
           (num-val (- 0 (expval->num (car expvals)))))
         (list exp1)))))

(define zero?-exp
  (lambda (exp1)
    (if (not (expression? exp1))
        (eopl:error "error")
        (op-exp
         (lambda (expvals)
           (if (= 0 (expval->num (car expvals)))
               (bool-val #t)
               (bool-val #f)))
         (list exp1)))))

(define list-exp
  (lambda (exps)
    (if (not ((list-of expression?) exps))
        (eopl:error "error")
        (op-exp
         (lambda (expvals)
           (list-val (map (lambda (ev) (expval->scheme-val ev)) expvals)))
         exps))))

;;; test
(define code1
  (let*-exp
    '(x y)
    (list
     (diff-exp (var-exp 'x) (const-exp 1))
     (diff-exp (var-exp 'x) (const-exp 3)))
    (diff-exp (var-exp 'x) (var-exp 'y))))
(check-equal? (value-of code1 (init-env)) (num-val 3))

     