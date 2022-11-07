#lang eopl
(require rackunit)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Senv = Listof(Sym)
; Lexaddr = N
; empty-senv : () → Senv
(define empty-senv
  (lambda ()
    '()))

; extend-senv : Var × Senv → Senv
(define extend-senv
  (lambda (var senv)
    (cons var senv)))

; apply-senv : Senv × Var → Lexaddr
(define apply-senv
  (lambda (senv var)
    (cond
      ((null? senv)
       (eopl:error 'report-unbound-var ))
      ((eqv? var (car senv))
       0)
      (else
       (+ 1 (apply-senv (cdr senv) var))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
  (cond-exp
   (conds (list-of expression?))
   (conseqs (list-of expression?)))
  (zero?-exp
   (exp1 expression?))
  (var-exp
   (var identifier?))
  (nameless-var-exp
   (num number?))
  (diff-exp
   (exp1 expression?)
   (exp2 expression?))
  (let-exp
   (var  identifier?)
   (exp  expression?)
   (body expression?))
  (nameless-let-exp
   (exp1 expression?)
   (body expression?))
  (proc-exp
   (var identifier?)
   (body expression?))
  (nameless-proc-exp
   (body expression?))
  (call-exp
   (rator expression?)
   (rand expression?))
  )

(define-datatype program program?
  (a-program
   (exp1 expression?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; translation-of-program : Program → Nameless-program

; init-senv : () → Senv
(define init-senv
  (lambda ()
    (extend-senv 'i
                 (extend-senv 'v
                              (extend-senv 'x
                                           (empty-senv))))))

(define translation-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (a-program
                  (translation-of exp1 (init-senv)))))))

; translation-of : Exp × Senv → Nameless-exp
(define translation-of
  (lambda (exp senv)
    (cases expression exp
      (const-exp (num) (const-exp num))
      (diff-exp (exp1 exp2)
                (diff-exp
                 (translation-of exp1 senv)
                 (translation-of exp2 senv)))
      (zero?-exp (exp1)
                 (zero?-exp
                  (translation-of exp1 senv)))
      (if-exp (exp1 exp2 exp3)
              (if-exp
               (translation-of exp1 senv)
               (translation-of exp2 senv)
               (translation-of exp3 senv)))
      (cond-exp (conds conseqs)
                (cond-exp (map (lambda (a-cond) (translation-of a-cond senv)) conds)
                          (map (lambda (conseq) (translation-of conseq senv)) conseqs)))
      (var-exp (var)
               (nameless-var-exp
                (apply-senv senv var)))
      (let-exp (var exp1 body)
               (nameless-let-exp
                (translation-of exp1 senv)
                (translation-of body
                                (extend-senv var senv))))
      (proc-exp (var body)
                (nameless-proc-exp
                 (translation-of body
                                 (extend-senv var senv))))
      (call-exp (rator rand)
                (call-exp
                 (translation-of rator senv)
                 (translation-of rand senv)))
      (else
       (eopl:error 'report-invalid-source-expression)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;  Nameless Interpreter
; procedure : Nameless-exp × Nameless-env → Proc
(define-datatype proc proc?
  (procedure
   (body expression?)
   (saved-nameless-env nameless-environment?)))
; apply-procedure : Proc × ExpVal → ExpVal
(define apply-procedure
  (lambda (proc1 val)
    (cases proc proc1
      (procedure (body saved-nameless-env)
                 (value-of body
                           (extend-nameless-env val saved-nameless-env))))))

(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val (proc proc?))
  )

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

; nameless-environment? : SchemeVal → Bool
(define nameless-environment?
  (lambda (x)
    ((list-of expval?) x)))
; empty-nameless-env : () → Nameless-env
(define empty-nameless-env
  (lambda ()
    '()))
; extend-nameless-env : ExpVal × Nameless-env → Nameless-env
(define extend-nameless-env
  (lambda (val nameless-env)
    (cons val nameless-env)))
; apply-nameless-env : Nameless-env × Lexaddr → ExpVal
(define apply-nameless-env
  (lambda (nameless-env n)
    (list-ref nameless-env n)))

;value-of : Nameless-exp × Nameless-env → ExpVal
(define value-of
  (lambda (exp nameless-env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (diff-exp (exp1 exp2)
                (let ((val1 (value-of exp1 nameless-env))
                      (val2 (value-of exp2 nameless-env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                    (num-val
                     (- num1 num2)))))
      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 nameless-env)))
                (if (expval->bool val1)
                    (value-of exp2 nameless-env)
                    (value-of exp3 nameless-env))))
      (cond-exp (conds conseqs)
                (let try-conds ([conds conds]
                                [conseqs conseqs])
                  (if (null? conds)
                      (eopl:error "value-of cond-exp")
                      (if (expval->bool (value-of (car conds) nameless-env))
                          (value-of (car conseqs) nameless-env)
                          (try-conds (cdr conds) (cdr conseqs))))))
      (zero?-exp (exp1)
                 (let ((val1 (value-of exp1 nameless-env)))
                   (let ((num1 (expval->num val1)))
                     (if (zero? num1)
                         (bool-val #t)
                         (bool-val #f)))))
      (call-exp (rator rand)
                (let ((proc (expval->proc (value-of rator nameless-env)))
                      (arg (value-of rand nameless-env)))
                  (apply-procedure proc arg)))

      (nameless-var-exp (n)
                        (apply-nameless-env nameless-env n))

      (nameless-let-exp (exp1 body)
                        (let ((val (value-of exp1 nameless-env)))
                          (value-of body
                                    (extend-nameless-env val nameless-env))))
      (nameless-proc-exp (body)
                         (proc-val
                          (procedure body nameless-env)))
      (else
       (eopl:error "Invalid Translated Expressionexp ~s" exp)))))

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
    (program (expression) a-program)
    (expression (number) const-exp)
    (expression (identifier) var-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("cond" (arbno expression "==>" expression) "end") cond-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    (expression ("(" expression expression ")") call-exp)
    ))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar-spec))

;;; Run
; value-of-program : Nameless-program → ExpVal
(define init-nameless-env
  (lambda () (extend-nameless-env (num-val 1)
                                  (extend-nameless-env (num-val 5)
                                                       (extend-nameless-env (num-val 10)
                                                                            (empty-nameless-env))))))
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (value-of exp1 (init-nameless-env))))))

; run : String → ExpVal
(define run
  (lambda (string)
    (value-of-program
     (translation-of-program
      (scan&parse string)))))


;;; test
(define source1
  "cond zero?(2) ==> 2
        zero?(1) ==> 1
        zero?(0) ==> 0
        zero?(-1) ==> -1
    end")


(define target1
  (translation-of-program (scan&parse source1)))
(check-equal? target1 (a-program
                       (cond-exp
                        (list
                         (zero?-exp (const-exp 2))
                         (zero?-exp (const-exp 1))
                         (zero?-exp (const-exp 0))
                         (zero?-exp (const-exp -1)))
                        (list (const-exp 2) (const-exp 1) (const-exp 0) (const-exp -1)))))

(check-equal? (run source1) (num-val 0))