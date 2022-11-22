#lang eopl
(require rackunit)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; contains expression
(define empty-env (lambda () '()))

(define extend-env-known (lambda (var exp env) (cons (list 'known var exp) env)))
(define extend-env-unknown (lambda (var env) (cons (list 'unknown var) env)))
(define env-record-type (lambda (record) (car record)))
(define env-record-var  (lambda (record) (cadr record)))
(define env-record-known-exp (lambda (record) (caddr record)))

(define apply-env-unknown-addr
  (lambda (env var)
    (let go ((env env)
             (addr 0))
      (if (null? env)
          (eopl:error 'report-unbound-var)
          (let ((record (car env)))
            (if (eqv? 'unknown (env-record-type record))
                (if (eqv? var (env-record-var record))
                    addr
                    (go (cdr env) (+ addr 1)))
                (go (cdr env) addr)))))))

(define apply-env-known-exp
  (lambda (env var)
    (if (null? env)
        (eopl:error "apply-env-known-exp: report-unbound-var ~s" var)
        (let ((record (car env)))
          (if (eqv? 'known (env-record-type record))
              (if (eqv? var (env-record-var record))
                  (env-record-known-exp record)
                  (apply-env-known-exp (cdr env) var))
              (apply-env-known-exp (cdr env) var))))))

(define known?
  (lambda (env var)
    (cond ((null? env)  #f)
          ((eqv? var (env-record-var  (car env)))
           (eqv? 'known (env-record-type (car env))))
          (else (known? (cdr env) var)))))
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
(define init-env
  (lambda () (empty-env)))

(define translation-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (a-program
                  (translation-of exp1 (init-env)))))))

; translation-of : Exp × Senv → Nameless-exp
(define translation-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (const-exp num))
      (diff-exp (exp1 exp2)
                (diff-exp
                 (translation-of exp1 env)
                 (translation-of exp2 env)))
      (zero?-exp (exp1)
                 (zero?-exp
                  (translation-of exp1 env)))
      (if-exp (exp1 exp2 exp3)
              (if-exp
               (translation-of exp1 env)
               (translation-of exp2 env)
               (translation-of exp3 env)))
      (var-exp (var)
               (if (known? env var)
                   (apply-env-known-exp env var)
                   (nameless-var-exp (apply-env-unknown-addr env var))))
      (let-exp (var exp1 body)
        (let ((trans-exp1 (translation-of exp1 env)))
               (nameless-let-exp
                trans-exp1
                (translation-of body
                                (extend-env-known var trans-exp1 env)))))
      (proc-exp (var body)
                (nameless-proc-exp
                 (translation-of body
                                 (extend-env-unknown var env))))
      (call-exp (rator rand)
                (call-exp
                 (translation-of rator env)
                 (translation-of rand env)))
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
        (value-of body nameless-env))
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
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    (expression ("(" expression expression ")") call-exp)
    ))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar-spec))

;;; Run
; value-of-program : Nameless-program → ExpVal
(define init-nameless-env
  (lambda () (empty-nameless-env)))
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


;;;test
(define source1
  "let x = 37
   in let f = proc (y)
               let z = -(y,x)
               in -(x,y)
      in (f 10)
  ")

(define target1
  (translation-of-program (scan&parse source1)))
(check-equal? (run source1) (num-val 27))

(define source2
  "let g = 10
   in let f1 = proc (x) -(x, 1)
      in let f2 = proc (y) (f1 g)
         in (f2 10)"
)

(define target2
  (translation-of-program (scan&parse source2)))
(check-equal? (run source2) (num-val 9))

(define source3
  "let x = 3
   in let f = proc (y) -(y,x)
      in (f 13)")
(define target3
  (translation-of-program (scan&parse source3)))
(check-equal? (run source3) (num-val 10))


(define source4
  "let f = proc (x) proc (y) -(y,-(0, x))
      in ((f 3) 4)"
      )
(define target4
  (translation-of-program (scan&parse source4)))
(check-equal? (run source4) (num-val 7))