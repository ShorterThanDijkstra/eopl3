#lang eopl
(require rackunit)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal data type
(define-datatype expval expval?
  (num-val
   (value number?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal -> scheme value
(define expval->num
  (lambda (v)
    (define expval-extractor-error
      (lambda (variant value)
        (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
                    	variant value)))
    (cases expval v
      	(num-val (num) num)
      	(else (expval-extractor-error 'num v)))))


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
   (var identifier?)
   (exp1 expression?)
   (body expression?))
  (op-exp
   (op procedure?) ;;; list of ExpVal -> ExpVal
   (exps (list-of expression?)))
  (cond-exp
   (conds (list-of (lambda (left&right)
                     (and (expression? (car left&right))
                          (expression? (cadr left&right)))))))
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
                (if (not (= (expval->num val1) 0))
                    (value-of exp2 env)
                    (value-of exp3 env))))
      (let-exp (var exp1 body)
               (let ((val1 (value-of exp1 env)))
                 (value-of body
                           (extend-env var val1 env))))
      (op-exp (op exps)
              (op
               (map (lambda (exp) (value-of exp env)) exps))) ;;; list of ExpVal
      (cond-exp (conds)
                (let find ([conds conds])
                  (if (null? conds)
                      (eopl:error "error")
                      (let* ([first-cond (car conds)]
                             [cond-left-exp (car first-cond)]
                             [cond-right-exp (cadr first-cond)]
                             [cond-left-expval (value-of cond-left-exp env)])
                        (if (not (= (expval->num cond-left-expval) 0))
                            (value-of cond-right-exp env)
                            (find (cdr conds)))))))

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
               (num-val 1)
               (num-val 0)))
         (list exp1)))))

;;; test
(define ast1
  (cond-exp
   (list
    (list (zero?-exp (const-exp 1)) (const-exp 0))
    (list (zero?-exp (const-exp 1)) (const-exp 1))
    (list (zero?-exp (const-exp 0)) (const-exp 2))
    (list (zero?-exp (const-exp 1)) (const-exp 3)))))

(check-equal? (value-of ast1 (init-env)) (num-val 2))

(define ast2
  (cond-exp
   (list
    (list (zero?-exp (const-exp 1)) (const-exp 0))
    (list (zero?-exp (const-exp 1)) (const-exp 1))
    (list (zero?-exp (const-exp 1)) (const-exp 2))
    (list (zero?-exp (const-exp 1)) (const-exp 3)))))

; (value-of ast2 (init-env))
