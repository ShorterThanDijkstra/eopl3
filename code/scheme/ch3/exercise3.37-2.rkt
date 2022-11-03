#lang eopl
(require rackunit)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Procedure data type
; procedure : Var × Exp × Env → Proc
(define-datatype proc proc?
  (procedure
   (var identifier?)
   (body expression?)
   ))
; apply-procedure : Proc × ExpVal → ExpVal
(define apply-procedure
  (lambda (proc1 val saved-env)
    (cases proc proc1
      (procedure (var body )
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
  (lambda (v)
    (cases expval v
      	(num-val (num) num)
      	(else (eopl:error)))))

(define expval->bool
  (lambda (v)
    (cases expval v
      	(bool-val (bool) bool)
      	(else (eopl:error)))))

(define expval->proc
  (lambda (v)
    (cases expval v
      	(proc-val (proc) proc)
      	(else (eopl:error)))))

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
  (lambda (proc-names bound-vars proc-bodies old-env)
    (if (null? proc-names)
        old-env
        (extend-env (car proc-names ) (proc-val (procedure (car bound-vars) (car proc-bodies)))
                    (extend-env-list (cdr proc-names) (cdr bound-vars) (cdr proc-bodies) old-env)))))

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
   (exp1 expression?))
  (var-exp
   (var identifier?))
  (diff-exp
   (exp1 expression?)
   (exp2 expression?))
  (mul-exp
   (exp1 expression?)
   (exp2 expression?))
  (let-exp
   (p-names (list-of identifier?))
   (b-vars (list-of identifier?))
   (p-bodies (list-of expression?))
   (let-body expression?))
  (proc-exp
   (var identifier?)
   (body expression?))
  (call-exp
   (rator expression?)
   (rand expression?))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter

; value-of : Exp × Env → ExpVal
(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (var-exp (var) (apply-env env var))
      (diff-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                    (num-val
                     (- num1 num2)))))
      (mul-exp (exp1 exp2)
               (let ((val1 (value-of exp1 env))
                     (val2 (value-of exp2 env)))
                 (let ((num1 (expval->num val1))
                       (num2 (expval->num val2)))
                   (num-val
                    (* num1 num2)))))
      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 env)))
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      (zero?-exp (exp1)
                 (let ((val1 (value-of exp1 env)))
                   (let ((num1 (expval->num val1)))
                     (if (zero? num1)
                         (bool-val #t)
                         (bool-val #f)))))
      (let-exp (proc-names bound-vars proc-bodies let-body)
                  (value-of let-body (extend-env-list proc-names bound-vars proc-bodies env)))
      (proc-exp (var body)
                (proc-val (procedure var body)))
      (call-exp (rator rand)
                (let ((proc (expval->proc (value-of rator env)))
                      (arg (value-of rand env)))
                  (apply-procedure proc arg env)))
      )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; parse
(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)
    ))

(define the-grammar-spec
  '(
    (expression (number) const-exp)
    (expression (identifier) var-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("*" "(" expression "," expression ")") mul-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" (arbno identifier "(" identifier ")" "=" expression) "in" expression) let-exp)
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    (expression ("(" expression expression ")") call-exp)
    ))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar-spec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define init-env
  (lambda ()
    (extend-env 'true (bool-val #t)
                (extend-env 'false (bool-val #f)
                            (empty-env)))))


(define run
  (lambda (code)
    (value-of (scan&parse code) (init-env))))

;;; test
(define code1
  "let fact(n) =  -(n, -1)
   in let fact(n) =
                  if zero?(n)
                  then 1
                  else *(n, (fact -(n,1)))
      in (fact 5)"
  )
(check-equal? (run code1) (num-val 120))
; dynamic binding: 120


; Write the mutually recursive procedures
; even and odd as in section 3.4 in the defined language with dynamic binding.
(define code2
  "let even(x) = if zero?(x) then true else (odd -(x, 1))
      odd(x) = if zero?(x) then false else (even -(x, 1))
  in (even 114)")

(check-equal? (run code2) (bool-val #t))

(define code3
  "let even(x) = if zero?(x) then true else (odd -(x, 1))
      odd(x) = if zero?(x) then false else (even -(x, 1))
  in (even 113)")

(check-equal? (run code3) (bool-val #f))


(define code4
  "let even(x) = if zero?(x) then true else (odd -(x, 1))
      odd(x) = if zero?(x) then false else (even -(x, 1))
  in (odd 514)")

(check-equal? (run code4) (bool-val #f))

(define code5
  "let even(x) = if zero?(x) then true else (odd -(x, 1))
      odd(x) = if zero?(x) then false else (even -(x, 1))
  in (odd 515)")

(check-equal? (run code5) (bool-val #t))