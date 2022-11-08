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

(define extend-senv-list
  (lambda (vars senv)
    (if (null? vars)
        senv
        (extend-senv (car vars) (extend-senv-list (cdr vars) senv)))))

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
  (zero?-exp
   (exp1 expression?))
  (var-exp
   (var identifier?))
  (cons-exp
   (first expression?)
   (second expression?))
  (car-exp
   (pair expression?))
  (cdr-exp
   (pair expression?))
  (nameless-var-exp
   (num number?))
  (nil-exp)
  (unpack-exp
   (vars (list-of identifier?))
   (exps expression?)
   (body expression?))
  (nameless-unpack-exp
   (exps expression?)
   (body expression?))
  (diff-exp
   (exp1 expression?)
   (exp2 expression?))
  (let-exp
   (var  identifier?)
   (lst-exp  expression?)
   (body expression?))
  (nameless-let-exp
   (lst-exp expression?)
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

(define cons-exp-len
  (lambda (exp)
    (cases expression exp
      (cons-exp
       (fst snd)
       (+ 1 (cons-exp-len snd)))
      (nil-exp () 0)
      (else (eopl:error 'cons-exp-len)))))

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
      (cons-exp (fst snd)
                (cons-exp
                 (translation-of fst senv)
                 (translation-of snd senv)))
      (car-exp (exp1)
               (car-exp (translation-of exp1 senv)))
      (cdr-exp (exp1)
               (cdr-exp (translation-of exp1 senv)))
      (nil-exp () (nil-exp))
      (unpack-exp (vars cons-exp body)
                  (if (not (= (length vars)
                              (cons-exp-len cons-exp)))
                      (eopl:error "unpack mismatch")
                      (nameless-unpack-exp (translation-of cons-exp senv)
                                           (translation-of body (extend-senv-list vars senv)))))
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
  (proc-val
   (proc proc?))
  (pair-val
   (fst expval?)
   (snd expval?))
  (nil-val)
  )

(define expval->num
  (lambda (v)
    (cases expval v
      	(num-val (num) num)
      	(else (eopl:error 'expval->num)))))

(define expval->bool
  (lambda (v)
    (cases expval v
      	(bool-val (bool) bool)
      	(else (eopl:error 'expval->bool)))))

(define expval->proc
  (lambda (v)
    (cases expval v
      	(proc-val (proc) proc)
      	(else (eopl:error 'expval->proc)))))

(define expval->pair-fst
  (lambda (v)
    (cases expval v
      	(pair-val (fst snd) fst)
      	(else (eopl:error 'expval->pair-fst)))))

(define expval->nil
  (lambda (v)
    (cases expval v
      	(nil-val () 'nil)
      	(else (eopl:error 'expval->nil)))))

(define expval->pair-snd
  (lambda (v)
    (cases expval v
      	(pair-val (fst snd) snd)
      	(else (eopl:error 'expval->pair-snd)))))

(define expval->scheme-val
  (lambda (v)
    (cases expval v
      (num-val (num) num)
      (bool-val (bool) bool)
      (proc-val (proc) proc)
      (pair-val (fst snd) (cons fst snd))
      (nil-val () 'nil)
      )))

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


(define extend-nameless-env-list
  (lambda (expvals nameless-env)
    (if (null? expvals)
        nameless-env
        (extend-nameless-env (car expvals)
                             (extend-nameless-env-list (cdr expvals) nameless-env)))))

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
      (cons-exp (fst snd)
                (pair-val (value-of fst nameless-env)
                          (value-of snd nameless-env)))
      (car-exp (exp1)
               (expval->pair-fst (value-of exp1 nameless-env)))
      (cdr-exp (exp1)
               (expval->pair-snd (value-of exp1 nameless-env)))
      (nil-exp ()
               (nil-val))
      (nameless-var-exp (n)
                        (apply-nameless-env nameless-env n))

      (nameless-let-exp (exp1 body)
                        (let ((val (value-of exp1 nameless-env)))
                          (value-of body
                                    (extend-nameless-env val nameless-env))))
      (nameless-unpack-exp (cons-exp body)
                           (letrec ((pair-val->list (lambda (pair)
                                                      (if (equal? pair (nil-val))
                                                          '()
                                                          (cons (expval->pair-fst pair)
                                                                (pair-val->list (expval->pair-snd pair)))))))
                             (let* ((cons-vals (value-of cons-exp nameless-env))
                                    (expvals (pair-val->list cons-vals)))
                               (value-of body (extend-nameless-env-list expvals nameless-env)))))
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
    (expression ("cons(" expression "," expression ")") cons-exp)
    (expression ("car" expression) car-exp)
    (expression ("cdr" expression) cdr-exp)
    (expression ("nil") nil-exp)
    (expression ("unpack" (arbno identifier) "=" expression "in" expression) unpack-exp)
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


;;;test
(define source1
  "let u = 30
   in let lst =  cons(u,cons(3,nil))
      in car lst
  ")

(define target1
  (translation-of-program (scan&parse source1)))

(check-equal? target1 (a-program
                       (nameless-let-exp
                        (const-exp 30)
                        (nameless-let-exp
                         (cons-exp (nameless-var-exp 0) (cons-exp (const-exp 3) (nil-exp)))
                         (car-exp (nameless-var-exp 0))))))
(check-equal? (run source1) (num-val 30))

(define source2
  "let u = 30
   in let lst =  cons(u,cons(3,nil))
      in cdr cdr lst
  ")

(define target2
  (translation-of-program (scan&parse source2)))

(check-equal? target2 (a-program
                       (nameless-let-exp
                        (const-exp 30)
                        (nameless-let-exp
                         (cons-exp (nameless-var-exp 0) (cons-exp (const-exp 3) (nil-exp)))
                         (cdr-exp (cdr-exp (nameless-var-exp 0)))))))
(check-equal? (run source2) (nil-val))


(define source3
  "let u = 30
   in let lst =  cons(u,cons(3,nil))
      in car cdr lst
  ")

(define target3
  (translation-of-program (scan&parse source3)))

(check-equal? target3 (a-program
                       (nameless-let-exp
                        (const-exp 30)
                        (nameless-let-exp
                         (cons-exp (nameless-var-exp 0) (cons-exp (const-exp 3) (nil-exp)))
                         (car-exp (cdr-exp (nameless-var-exp 0)))))))

(check-equal? (run source3) (num-val 3))

(define source4
  "let u = 7
   in unpack x y = cons(u,cons(3,nil))
      in -(x,y)
")
(define target4
  (translation-of-program (scan&parse source4)))

(check-equal? target4
              (a-program
               (nameless-let-exp
                (const-exp 7)
                (nameless-unpack-exp
                 (cons-exp (nameless-var-exp 0) (cons-exp (const-exp 3) (nil-exp)))
                 (diff-exp (nameless-var-exp 0) (nameless-var-exp 1))))))

(check-equal? (run source4) (num-val 4))

(define source5
  "let u = 7
   in unpack a b c d = cons(u,cons(3,nil))
      in d
")
; (run source5) ; error