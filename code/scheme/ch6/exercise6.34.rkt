#lang eopl
(require rackunit)
(require racket/format)
(require racket/string)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Procedure data type
(define-datatype proc
  proc?
  (procedure (vars (list-of identifier?))
             (body expression?)
             (saved-env environment?)))

(define apply-procedure
  (lambda (proc1 vals)
    (cases proc
      proc1
      (procedure (vars body saved-env)
                 (value-of body (extend-env-list vars vals saved-env))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal data type
(define-datatype expval
  expval?
  (num-val (value number?))
  (bool-val (boolean boolean?))
  (proc-val (proc proc?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal -> scheme value
(define expval->num
  (lambda (v) (cases expval v (num-val (num) num) (else (eopl:error)))))

(define expval->bool
  (lambda (v) (cases expval v (bool-val (bool) bool) (else (eopl:error)))))

(define expval->proc
  (lambda (v) (cases expval v (proc-val (proc) proc) (else (eopl:error)))))

(define expval->scheme-val
  (lambda (v)
    (cases expval
      v
      (num-val (num) num)
      (bool-val (bool) bool)
      (proc-val (proc) proc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Env
(define-datatype environment
  environment?
  (empty-env)
  (extend-env (var identifier?) (val expval?) (env environment?))
  (extend-env-rec-list (p-names (list-of identifier?))
                       (b-varss (list-of (list-of identifier?)))
                       (bodies (list-of expression?))
                       (env environment?)))

(define apply-env
  (lambda (env search-var)
    (cases
        environment
      env
      (empty-env () (eopl:error 'apply-env "~s" search-var))
      (extend-env (saved-var saved-val saved-env)
                  (if (eqv? saved-var search-var)
                      saved-val
                      (apply-env saved-env search-var)))
      (extend-env-rec-list
       (p-names b-varss p-bodies saved-env)
       (let search ([p-names p-names] [b-varss b-varss] [p-bodies p-bodies])
         (if (null? p-names)
             (apply-env saved-env search-var)
             (if (eqv? (car p-names) search-var)
                 (proc-val (procedure (car b-varss) (car p-bodies) env))
                 (search (cdr p-names) (cdr b-varss) (cdr p-bodies)))))))))

(define extend-env-list
  (lambda (vars vals env)
    (if (null? vars)
        env
        (extend-env (car vars)
                    (car vals)
                    (extend-env-list (cdr vars) (cdr vals) env)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter
; value-of : Exp × Env → ExpVal
(define value-of
  (lambda (exp env)
    (cases
        expression
      exp
      (const-exp (num) (num-val num))
      (var-exp (var) (apply-env env var))
      (diff-exp (exp1 exp2)
                (let ([val1 (value-of exp1 env)] [val2 (value-of exp2 env)])
                  (let ([num1 (expval->num val1)] [num2 (expval->num val2)])
                    (num-val (- num1 num2)))))
      (sum-exp
       (exps)
       (let ([vals (map (lambda (exp1) (expval->num (value-of exp1 env))) exps)])
         (let loop ([vals vals] [res 0])
           (if (null? vals)
               (num-val res)
               (loop (cdr vals) (+ res (car vals)))))))
      (if-exp
       (exp1 exp2 exp3)
       (let ([val1 (value-of exp1 env)])
         (if (expval->bool val1) (value-of exp2 env) (value-of exp3 env))))
      (zero?-exp (exp1)
                 (let ([val1 (value-of exp1 env)])
                   (let ([num1 (expval->num val1)])
                     (if (zero? num1) (bool-val #t) (bool-val #f)))))
      (let-exp (var exp body)
               (value-of body (extend-env var (value-of exp env) env)))
      (letrec-exp
       (proc-names bound-varss proc-bodies letrec-body)
       (value-of letrec-body
                 (extend-env-rec-list proc-names bound-varss proc-bodies env)))
      (proc-exp (vars body) (proc-val (procedure vars body env)))
      (call-exp (rator rands)
                (let ([proc (expval->proc (value-of rator env))]
                      [args (map (lambda (rand) (value-of rand env)) rands)])
                  (apply-procedure proc args))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define init-env
  (lambda ()
    (extend-env 'true
                (bool-val #t)
                (extend-env 'false (bool-val #f) (empty-env)))))

(define value-of-program
  (lambda (pgm)
    (cases program
      pgm
      (a-program (exp1) (value-of exp1 (init-env))))))

;;; run
(define run (lambda (code) (value-of-program (scan&parse code))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; unparse
(define unparse-exp
  (lambda (exp)
    (cases
        expression
      exp
      (const-exp (num) (~a num))
      (var-exp (var) (~a var))
      (diff-exp (exp1 exp2)
                (~a "-" "(" (unparse-exp exp1) ", " (unparse-exp exp2) ")"))
      (sum-exp (exps)
               (let ([unparsed (map unparse-exp exps)])
                 (if (null? unparsed)
                     "+()"
                     (let loop ([rest (cdr unparsed)]
                                [res (~a "+(" (car unparsed))])
                       (if (null? rest)
                           (~a res ")")
                           (loop (cdr rest) (~a res ", " (car rest))))))))
      (if-exp (exp1 exp2 exp3)
              (~a " if " (unparse-exp exp1)
                  " then " (unparse-exp exp2)
                  " else " (unparse-exp exp3)))
      (zero?-exp (exp1)
                 (~a "zero?" "(" (unparse-exp exp1) ")"))
      (let-exp (var rhs body)
               (~a "let" " " var " = " (unparse-exp rhs) " in " (unparse-exp body) " "))
      (letrec-exp
       ( p-names b-varss p-bodies letrec-body)
       (let ((unparsed-procs (map (lambda (p-name b-vars p-body)
                                    (~a p-name b-vars " = " (unparse-exp p-body)))
                                  p-names b-varss p-bodies)))
         (let loop ([unparsed-procs unparsed-procs]
                    [res "letrec "])
           (if (null? unparsed-procs)
               (~a res " in " (unparse-exp letrec-body) " ")
               (loop (cdr unparsed-procs) (~a res (car unparsed-procs) "\n"))))))
      (proc-exp (vars body) (~a "proc" (~a vars) " " (unparse-exp body)))
      (call-exp (rator rands)
                (let ([unparsed-rator (unparse-exp rator)]
                      [unparsed-rands (map unparse-exp rands)])
                  (let loop ([unparsed-rands unparsed-rands]
                             [res (~a "(" unparsed-rator)])
                    (if (null? unparsed-rands)
                        (~a res ")")
                        (loop (cdr unparsed-rands) (~a res " " (car unparsed-rands))))))))))

(define unparse
  (lambda (pgm)
    (cases program
      pgm
      (a-program (exp1)
                 (let ((unparsed (unparse-exp exp1)))
                   (string-replace unparsed "%" ""))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Helper Functions
(define list-set
  (lambda (lst n val)
    (cond
      [(null? lst) (eopl:error 'list-set "ran off end")]
      [(zero? n) (cons val (cdr lst))]
      [else (cons (car lst) (list-set (cdr lst) (- n 1) val))])))

(define list-index
  (lambda (pred lst)
    (cond
      [(null? lst) #f]
      [(pred (car lst)) 0]
      [(list-index pred (cdr lst))
       =>
       (lambda (n) (+ n 1))]
      [else #f])))

(define every?
  (lambda (pred lst)
    (cond
      [(null? lst) #t]
      [(pred (car lst)) (every? pred (cdr lst))]
      [else #f])))

(define identifier? (lambda (exp) (and (symbol? exp) (not (eqv? exp 'lambda)))))

(define fresh-identifier
  (let ([sn 0])
    (lambda (identifier)
      (set! sn (+ sn 1))
      (string->symbol
       (string-append (symbol->string identifier)
                      "%" ; this can't appear in an input identifier
                      (number->string sn))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Grammar
(define the-lexical-spec
  '([whitespace (whitespace) skip]
    [comment ("%" (arbno (not #\newline))) skip]
    [identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol]
    [number (digit (arbno digit)) number]
    [number ("-" digit (arbno digit)) number]))

(define the-grammar
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("+" "(" (separated-list expression ",") ")") sum-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression
     ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" expression)
               "in"
               expression)
     letrec-exp)
    (expression (identifier) var-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("proc" "(" (arbno identifier) ")" expression) proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)))

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; anf?
(define anf?
  (lambda (pgm)
    (cases program
      pgm
      (a-program (exp1)
                 (anf-exp? exp1)))))

(define anf-simple?
  (lambda (exp)
    (cases expression
      exp
      (const-exp (num) #t)
      (var-exp (var) #t)
      (proc-exp (vars body) (anf-exp? body))
      (zero?-exp (exp1) (anf-simple? exp1))
      (diff-exp (exp1 exp2) (and (anf-simple? exp1)
                                 (anf-simple? exp2)))
      (sum-exp (exps) (every? anf-simple? exps))
      (if-exp (exp1 exp2 exp3) (and (anf-simple? exp1)
                                    (anf-exp? exp2)
                                    (anf-exp? exp3)))
      (else #f))))

(define anf-call?
  (lambda (exp)
    (cases expression exp
      (call-exp (rator rands) (and (anf-simple? rator)
                                   (every? anf-simple? rands)))
      (else #t))))

(define call-exp?
  (lambda (exp)
    (cases expression exp
      (call-exp (rator rands) #t)
      (else #f))))

(define anf-exp?
  (lambda (exp)
    (cases
        expression
      exp
      (let-exp (var exp1 body)
               (if (call-exp? exp1)
                   (and (anf-call? exp1)
                        (anf-exp? body))
                   (and (anf-simple? exp1)
                        (anf-exp? body))))
      (letrec-exp (p-names b-varss p-bodies letrec-body)
                  (and (every? anf-exp? p-bodies)
                       (anf-exp? letrec-body)))
      (call-exp (rator rands) (and (anf-simple? rator)
                                   (every? anf-simple? rands)))
      (else (anf-simple? exp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Converter

(define anf-of-exps
  (lambda (exps builder)
    (if (= (length exps) 1)
        (builder (list (anf-of-exp (car exps))))
        (let anf-of-rest ([exps exps]
                          [acc '()])
          (cond [(null? exps)
                 (builder (reverse acc))]
                [(inp-exp-simple? (car exps))
                 (anf-of-rest (cdr exps)
                              (cons (car exps) acc))]
                [else (let ([var (fresh-identifier 'var)])
                        (let-exp var (anf-of-exp (car exps))
                                 (anf-of-rest (cdr exps)
                                              (cons (var-exp var) acc))))])))))

(define inp-exp-simple?
  (lambda (exp)
    (cases
        expression
      exp
      (const-exp (num) #t)
      (var-exp (var) #t)
      (diff-exp (exp1 exp2) (and (inp-exp-simple? exp1) (inp-exp-simple? exp2)))
      (zero?-exp (exp1) (inp-exp-simple? exp1))
      (proc-exp (ids exp) #t)
      (sum-exp (exps) (every? inp-exp-simple? exps))
      (else #f))))

(define anf-of-exp
  (lambda (exp)
    (cases
        expression
      exp
      (const-exp (num) exp)
      (var-exp (var) exp)
      (proc-exp (vars body) (anf-of-proc-exp vars body))
      (zero?-exp (exp1) (anf-of-zero?-exp exp1))
      (diff-exp (exp1 exp2) (anf-of-diff-exp exp1 exp2))
      (sum-exp (exps) (anf-of-sum-exp exps))
      (if-exp (exp1 exp2 exp3) (anf-of-if-exp exp1 exp2 exp3))
      (let-exp (var exp1 body) (anf-of-let-exp var exp1 body))
      (letrec-exp (p-names b-varss p-bodies letrec-body)
                  (anf-of-letrec-exp p-names b-varss p-bodies letrec-body))
      (call-exp (rator rands) (anf-of-call-exp rator rands)))))

(define anf-of-proc-exp
  (lambda (vars body)
    (proc-exp vars (anf-of-exp body))))

(define anf-of-sum-exp
  (lambda (exps)
    (anf-of-exps exps
                 (lambda (in-simples)
                   (sum-exp in-simples)))))

(define anf-of-call-exp
  (lambda (rator rands)
    (anf-of-exps (cons rator rands)
                 (lambda (in-simples)
                   (call-exp (car in-simples)
                             (cdr in-simples))))))

(define anf-of-zero?-exp
  (lambda (exp1)
    (anf-of-exps (list exp1)
                 (lambda (in-simples)
                   (zero?-exp (car in-simples))))))

(define anf-of-diff-exp
  (lambda (exp1 exp2)
    (anf-of-exps
     (list exp1 exp2)
     (lambda (in-simples)
       (diff-exp (car in-simples) (cadr in-simples))))))

(define anf-of-if-exp
  (lambda (exp1 exp2 exp3)
    (anf-of-exps (list exp1)
                 (lambda (in-simples)
                   (let ((var (fresh-identifier 'var)))
                     (let-exp var (car in-simples)
                              (if-exp (var-exp var)
                                      (anf-of-exp exp2)
                                      (anf-of-exp exp3))))))))

;;; ugly
(define anf-of-let-exp
  (lambda (id rhs body)
    (anf-of-exps (list rhs)
                 (lambda (ins)
                   (let ((in (car ins)))
                     (cases expression 
                       in
                       (let-exp (var exp1 let-body)
                                (let-exp var exp1
                                         (let-exp id let-body
                                                  (anf-of-exp body))))
                       (else (let-exp id in
                                      (anf-of-exp body)))))))))

(define anf-of-letrec-exp
  (lambda (p-names b-varss p-bodies letrec-body)
    (letrec-exp
     p-names
     b-varss
     (map (lambda (p-body) (anf-of-exp p-body)) p-bodies)
     (anf-of-exp letrec-body))))

(define anf-of-program
  (lambda (pgm)
    (cases program
      pgm
      (a-program (exp1)
                 (a-program (anf-of-exps (list exp1)
                                         (lambda (new-args)
                                           (car new-args))))))))

(define transform (lambda (str) (anf-of-program (scan&parse str))))

(provide transform)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; test

(define str0
  "letrec equal?(x n) = if zero?(x)
                             then zero?(n)
                             else (equal? -(x, 1) -(n, 1))
   in let f = proc(x) x
      in let g = proc(x y) +(x, y, 37)
         in let h = proc(x y z) +(x, y, z, 17)
            in let y = 73
               in let p = proc(x) if zero?(x)
                                  then 17
                                  else if (equal? x 1)
                                       then (f -(x, 13))
                                       else if (equal? x 2)
                                            then +(22, -(x, 3), x)
                                            else if (equal? x 3)
                                                 then +(22, (f x), 37)
                                                 else if (equal? x 4)
                                                      then (g 22 (f x))
                                                      else if (equal? x 5)
                                                           then +(22, (f x), 33, (g y 37))
                                                           else (h (f x) -(44, y) (g y 37))
                   in +((p 1), (p 2), (p 3), (p 4), (p 5), (p 73))")
(check-equal? (value-of-program (transform str0)) (num-val 551))
(check-true (anf? (transform str0)))
(check-false (anf? (scan&parse str0)))

(define str1
  "let f = proc(x) x
   in (f 73)")
(check-equal? (value-of-program (transform str1)) (num-val 73))
(check-true (anf? (transform str1)))
(check-true (anf? (scan&parse str1)))

(define str2
  "letrec less?(n m) = if zero?(m)
                       then false
                       else if zero?(n)
                            then true
                            else(less? -(n, 1) -(m, 1))
    in letrec fib(n) = if (less? n 2)
                       then n
                       else +((fib -(n, 1)), (fib -(n, 2)))
    in (fib 15)")
(check-equal? (value-of-program (transform str2)) (num-val 610))
(check-true (anf? (transform str2)))
(check-false (anf? (scan&parse str2)))

(define str3
  "let f = proc(x) x
   in +(73, (f 37), 12, (f 21))")
(check-equal? (value-of-program (transform str3)) (num-val 143))
(check-true (anf? (transform str3)))
(check-false (anf? (scan&parse str3)))

(define str4
  "let f = proc(x) x
   in let x = +((f 73), 37)
      in (f x)")
(check-equal? (value-of-program (transform str4)) (num-val 110))
(check-true (anf? (transform str4)))
(check-false (anf? (scan&parse str4)))
