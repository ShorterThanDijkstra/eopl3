#lang eopl
(require rackunit)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Senv = Listof(ListOf(Sym))
; Lexaddr = (Depth Posi)
; empty-senv : () → Senv
(define empty-senv
  (lambda ()
    '()))

; extend-senv : Var × Senv → Senv
(define extend-senv
  (lambda (vars senv)
    (cons vars senv)))

(define position
  (lambda (var vars posi)
    (cond ((null? vars)
           (eopl:error 'position))
          ((eqv? var (car vars))
           posi)
          (else (position var (cdr vars) (+ posi 1))))))

; apply-senv : Senv × Var → Lexaddr
(define apply-senv
  (lambda (senv var)
    (let search ((senv senv)
                 (depth 0))
      (cond
        ((null? senv)
         (eopl:error 'report-unbound-var ))
        ((memq var (car senv))
         (list depth (position var (car senv) 0)))
        (else
         (search (cdr senv) (+ depth 1)))))))

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
   (depth number?)
   (posi number?))
  (diff-exp
   (exp1 expression?)
   (exp2 expression?))
  (let-exp
   (vars  (list-of identifier?))
   (exps  (list-of expression?))
   (body expression?))
  (nameless-let-exp
   (exps (list-of expression?))
   (body expression?))
  (proc-exp
   (vars (list-of identifier?))
   (body expression?))
  (nameless-proc-exp
   (body expression?))
  (call-exp
   (rator expression?)
   (rand (list-of expression?)))
  )

(define-datatype program program?
  (a-program
   (exp1 expression?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; translation-of-program : Program → Nameless-program

; init-senv : () → Senv
(define init-senv empty-senv)

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
      (var-exp (var)
               (let ((depth&posi (apply-senv senv var)))
                 (nameless-var-exp (car depth&posi) (cadr depth&posi))))
      (let-exp (vars exps body)
               (nameless-let-exp
                (map (lambda (exp) (translation-of exp senv)) exps)
                (translation-of body
                                (extend-senv vars senv))))
      (proc-exp (vars body)
                (nameless-proc-exp
                 (translation-of body
                                 (extend-senv vars senv))))
      (call-exp (rator rands)
                (call-exp
                 (translation-of rator senv)
                 (map (lambda (rand) (translation-of rand senv)) rands)))
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
  (lambda (proc1 vals)
    (cases proc proc1
      (procedure (body saved-nameless-env)
                 (value-of body
                           (extend-nameless-env vals saved-nameless-env))))))

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
    ((list-of (list-of expval?)) x)))
; empty-nameless-env : () → Nameless-env
(define empty-nameless-env
  (lambda ()
    '()))
; extend-nameless-env : ExpVal × Nameless-env → Nameless-env
(define extend-nameless-env
  (lambda (vals nameless-env)
    (cons vals nameless-env)))
; apply-nameless-env : Nameless-env × Lexaddr → ExpVal
(define apply-nameless-env
  (lambda (nameless-env depth posi)
    (list-ref (list-ref nameless-env depth) posi)))

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
      (call-exp (rator rands)
                (let ((proc (expval->proc (value-of rator nameless-env)))
                      (args (map (lambda (rand) (value-of rand nameless-env)) rands)))
                  (apply-procedure proc args)))

      (nameless-var-exp (depth posi)
                        (apply-nameless-env nameless-env depth posi))

      (nameless-let-exp (exps body)
                        (let ((vals (map (lambda (exp) (value-of exp nameless-env)) exps)))
                          (value-of body
                                    (extend-nameless-env vals nameless-env))))
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
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp)
    (expression ("proc" "(" (arbno identifier) ")" expression) proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    ))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar-spec))

;;; Run
; value-of-program : Nameless-program → ExpVal
(define init-nameless-env empty-nameless-env)
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

(check-equal? (run source1) (num-val 27))
(define source2
  "
  let add = proc (x y) -(x, -(0, y))
      sub = proc (x y) -(x, y)
  in (add 114 (sub 51 4))
   "
  )

(check-equal? (run source2) (num-val 161))