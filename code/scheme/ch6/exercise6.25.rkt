#lang eopl
(require rackunit)
(require racket/format)
(require racket/string)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Procedure data type
(define-datatype proc
  proc?
  (procedure (vars (list-of identifier?))
             (body tfexp?)
             (saved-env environment?)))

; apply-procedure : Proc × ExpVal → ExpVal
(define apply-procedure/k
  (lambda (proc1 args cont)
    (cases proc
      proc1
      (procedure
       (vars body saved-env)
       (value-of/k body (extend-env* vars args saved-env) cont)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal data type
(define-datatype expval
  expval?
  (num-val (value number?))
  (bool-val (boolean boolean?))
  (proc-val (proc proc?))
  (list-val (vals (list-of expval?))))

(define expval->list
  (lambda (v)
    (cases expval
      v
      (list-val (lst) lst)
      (else (eopl:error 'expval->list "~s" v)))))

(define expval->num
  (lambda (v)
    (cases expval
      v
      (num-val (num) num)
      (else (eopl:error 'expval->num "~s" v)))))

(define expval->bool
  (lambda (v)
    (cases expval
      v
      (bool-val (bool) bool)
      (else (eopl:error 'expval->bool "~s" v)))))

(define expval->proc
  (lambda (v)
    (cases expval
      v
      (proc-val (proc) proc)
      (else (eopl:error 'expval->proc "~s" v)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Env
(define-datatype environment
  environment?
  (empty-env)
  (extend-env (var identifier?) (val expval?) (env environment?))
  (extend-env-rec** (p-names (list-of identifier?))
                    (b-varss (list-of (list-of identifier?)))
                    (bodies (list-of tfexp?))
                    (env environment?)))

(define apply-env
  (lambda (env search-var)
    (cases
        environment
      env
      (empty-env () (eopl:error 'apply-env))
      (extend-env (saved-var saved-val saved-env)
                  (if (eqv? saved-var search-var)
                      saved-val
                      (apply-env saved-env search-var)))
      (extend-env-rec**
       (p-names b-varss p-bodies saved-env)
       (let search ([p-names p-names] [b-varss b-varss] [p-bodies p-bodies])
         (if (null? p-names)
             (apply-env saved-env search-var)
             (if (eqv? (car p-names) search-var)
                 (proc-val (procedure (car b-varss) (car p-bodies) env))
                 (search (cdr p-names) (cdr b-varss) (cdr p-bodies)))))))))

(define extend-env*
  (lambda (vars vals env)
    (if (null? vars)
        env
        (extend-env (car vars)
                    (car vals)
                    (extend-env* (cdr vars) (cdr vals) env)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Expression && Parsing
(define identifier? (lambda (exp) (and (symbol? exp) (not (eqv? exp 'lambda)))))

(define cps-out-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define cps-out-grammar-spec
  '((cps-out-program (tfexp) cps-a-program)
    (simple-expression (number) cps-const-exp)
    (simple-expression (identifier) cps-var-exp)
    (simple-expression ("-" "(" simple-expression "," simple-expression ")")
                       cps-diff-exp)
    (simple-expression ("zero?" "(" simple-expression ")") cps-zero?-exp)
    (simple-expression ("+" "(" (separated-list simple-expression ",") ")")
                       cps-sum-exp)
    (simple-expression ("proc" "(" (arbno identifier) ")" tfexp) cps-proc-exp)
    (simple-expression ("list" "(" (separated-list simple-expression ",") ")")
                       cps-list-exp)
    (tfexp (simple-expression) simple-exp->exp)
    (tfexp ("let" (arbno identifier "=" simple-expression) "in" tfexp) cps-let-exp)
    (tfexp ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" tfexp)
                     "in"
                     tfexp)
           cps-letrec-exp)
    (tfexp ("if" simple-expression "then" tfexp "else" tfexp) cps-if-exp)
    (tfexp ("(" simple-expression (arbno simple-expression) ")") cps-call-exp)))

(define scan&parse
  (sllgen:make-string-parser cps-out-lexical-spec cps-out-grammar-spec))

(sllgen:make-define-datatypes cps-out-lexical-spec cps-out-grammar-spec)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Continuation
(define-datatype continuation continuation? (end-cont))

(define apply-cont
  (lambda (cont val) (cases continuation cont (end-cont () val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter
(define value-of-simple-exp
  (lambda (simple env)
    (cases
        simple-expression
      simple
      (cps-const-exp (num) (num-val num))
      (cps-var-exp (var) (apply-env env var))
      (cps-diff-exp (exp1 exp2)
                    (let ([val1 (value-of-simple-exp exp1 env)]
                          [val2 (value-of-simple-exp exp2 env)])
                      (let ([num1 (expval->num val1)] [num2 (expval->num val2)])
                        (num-val (- num1 num2)))))
      (cps-sum-exp
       (exps)
       (let ([vals (map (lambda (exp1)
                          (expval->num (value-of-simple-exp exp1 env)))
                        exps)])
         (let loop ([vals vals] [res 0])
           (if (null? vals)
               (num-val res)
               (loop (cdr vals) (+ res (car vals)))))))
      (cps-list-exp
       (exps)
       (list-val (map (lambda (exp1) (value-of-simple-exp exp1 env)) exps)))
      (cps-zero?-exp (exp1)
                     (let ([val1 (value-of-simple-exp exp1 env)])
                       (let ([num1 (expval->num val1)])
                         (if (zero? num1) (bool-val #t) (bool-val #f)))))
      (cps-proc-exp (vars body) (proc-val (procedure vars body env))))))

; value-of/k : TfExp × Env × Cont → FinalAnswer
(define value-of/k
  (lambda (exp env cont)
    (cases
        tfexp
      exp
      (simple-exp->exp (simple)
                       (apply-cont cont (value-of-simple-exp simple env)))
      (cps-let-exp (vars rhss body)
                   (let ([vals (map (lambda (rhs) (value-of-simple-exp rhs env)) rhss)])
                     (value-of/k body (extend-env* vars vals env) cont)))
      (cps-letrec-exp (p-names b-varss p-bodies letrec-body)
                      (value-of/k letrec-body
                                  (extend-env-rec** p-names b-varss p-bodies env)
                                  cont))
      (cps-if-exp (simple1 body1 body2)
                  (if (expval->bool (value-of-simple-exp simple1 env))
                      (value-of/k body1 env cont)
                      (value-of/k body2 env cont)))
      (cps-call-exp
       (rator rands)
       (let ([rator-proc (expval->proc (value-of-simple-exp rator env))]
             [rand-vals
              (map (lambda (simple) (value-of-simple-exp simple env)) rands)])
         (apply-procedure/k rator-proc rand-vals cont))))))

(define init-env
  (lambda ()
    (extend-env 'true
                (bool-val #t)
                (extend-env 'false (bool-val #f) (empty-env)))))

(define value-of-program
  (lambda (pgm)
    (cases cps-out-program
      pgm
      (cps-a-program (exp1) (value-of/k exp1 (init-env) (end-cont))))))

(define run (lambda (code) (value-of-program (scan&parse code))))

(define value-of-cps-out-program value-of-program)

(define unparse-simple
  (lambda (simple)
    (cases
        simple-expression
      simple
      (cps-const-exp (num) (~a num))
      (cps-var-exp (var) (~a var))
      (cps-diff-exp (exp1 exp2)
                    (~a "-" "(" (unparse-simple exp1) ", " (unparse-simple exp2) ")"))
      (cps-sum-exp
       (exps)
       (let ([unparsed (map unparse-simple exps)])
         (if (null? unparsed)
             "+()"
             (let loop ([rest (cdr unparsed)]
                        [res (~a "+(" (car unparsed))])
               (if (null? rest)
                   (~a res ")")
                   (loop (cdr rest) (~a res ", " (car rest))))))))
      (cps-list-exp (exps)
                    (let ([unparsed (map unparse-simple exps)])
                      (if (null? unparsed)
                          "list()"
                          (let loop ([rest (cdr unparsed)]
                                     [res (~a "list(" (car unparsed))])
                            (if (null? rest)
                                (~a res ")")
                                (loop (cdr rest) (~a res ", " (car rest))))))))
      (cps-zero?-exp (exp1)
                     (~a "zero?" "(" (unparse-simple exp1) ")"))
      (cps-proc-exp (vars body) (~a "proc" (~a vars) " " (unparse-tf body))))))

(define unparse-tf
  (lambda (exp)
    (cases
        tfexp
      exp
      (simple-exp->exp (simple)
                       (unparse-simple simple))
      (cps-let-exp (vars rhss body)
                   (let ((unparsed-items (map (lambda (var rhs)
                                                (~a var " = "(unparse-simple rhs)))
                                              vars rhss)))
                     (let loop ([unparsed-items unparsed-items]
                                [res "let "])
                       (if (null? unparsed-items)
                           (~a res " in " (unparse-tf body) " ")
                           (loop (cdr unparsed-items) (~a res (car unparsed-items)))))))
      (cps-letrec-exp (p-names b-varss p-bodies letrec-body)
                      (let ((unparsed-procs (map
                                             (lambda (p-name b-vars p-body)
                                               (~a p-name b-vars " = " (unparse-tf p-body)))
                                             p-names b-varss p-bodies)))
                        (let loop ([unparsed-procs unparsed-procs]
                                   [res "letrec "])
                          (if (null? unparsed-procs)
                              (~a res " in " (unparse-tf letrec-body) " ")
                              (loop (cdr unparsed-procs) (~a res (car unparsed-procs) "\n"))))))


      (cps-if-exp (simple1 body1 body2)
                  (~a " if " (unparse-simple simple1)
                      " then " (unparse-tf body1)
                      " else " (unparse-tf body2)))
      (cps-call-exp
       (rator rands)
       (let ([unparsed-rator (unparse-simple rator)]
             [unparsed-rands (map unparse-simple rands)])
         (let loop ([unparsed-rands unparsed-rands]
                    [res (~a "(" unparsed-rator)])
           (if (null? unparsed-rands)
               (~a res ")")
               (loop (cdr unparsed-rands) (~a res " " (car unparsed-rands))))))))))

(define unparse
  (lambda (pgm)
    (cases cps-out-program
      pgm
      (cps-a-program (exp1)
                     (let ((unparsed (unparse-tf exp1)))
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

(define fresh-identifier
  (let ([sn 0])
    (lambda (identifier)
      (set! sn (+ sn 1))
      (string->symbol
       (string-append (symbol->string identifier)
                      "%" ; this can't appear in an input identifier
                      (number->string sn))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; CPS In
(define cps-in-lexical-spec
  '([whitespace (whitespace) skip]
    [comment ("%" (arbno (not #\newline))) skip]
    [identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol]
    [number (digit (arbno digit)) number]
    [number ("-" digit (arbno digit)) number]))

(define cps-in-grammar
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("+" "(" (separated-list expression ",") ")") sum-exp)
    (expression ("list" "(" (separated-list expression ",") ")") list-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression
     ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" expression)
               "in"
               expression)
     letrec-exp)
    (expression (identifier) var-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp)
    (expression ("proc" "(" (arbno identifier) ")" expression) proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)))

(sllgen:make-define-datatypes cps-in-lexical-spec cps-in-grammar)

(define scan&parse-cps-in
  (sllgen:make-string-parser cps-in-lexical-spec cps-in-grammar))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Converter

; make-send-to-cont : SimpleExp × SimpleExp → TfExp
(define make-send-to-cont
  (lambda (k-exp simple-exp) (cps-call-exp k-exp (list simple-exp))))

(define report-invalid-exp-to-cps-of-simple-exp
  (lambda (exp)
    (eopl:error 'cps-simple-of-exp
                "non-simple expression to cps-of-simple-exp: ~s"
                exp)))

; cps-of-exps : Listof(InpExp) × (Listof(InpExp) → TfExp) → TfExp
(define cps-of-exps
  (lambda (exps builder)
    (let cps-of-rest ([exps exps])
      ;   cps-of-rest : Listof(InpExp) → TfExp
      (let ([pos (list-index (lambda (exp) (not (inp-exp-simple? exp))) exps)])
        ; (when pos
        ;   (display (list-ref exps pos))
        ;   (newline)
        ;   (newline))
        (if (not pos)
            (builder (map cps-of-simple-exp exps))
            (let ([var (fresh-identifier 'var)])
              (cps-of-exp (list-ref exps pos)
                          (cps-proc-exp
                           (list var)
                           (cps-of-rest
                            (list-set exps pos (var-exp var)))))))))))

; inp-exp-simple? : InpExp → Bool
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
      (list-exp (exps) (every? inp-exp-simple? exps))
      (else #f))))

; cps-of-exp : InpExp × SimpleExp → TfExp
(define cps-of-exp
  (lambda (exp k-exp)
    (cases
        expression
      exp
      (const-exp (num) (make-send-to-cont k-exp (cps-const-exp num)))
      (var-exp (var) (make-send-to-cont k-exp (cps-var-exp var)))
      (proc-exp (vars body)
                (make-send-to-cont
                 k-exp
                 (cps-proc-exp (append vars (list 'k%00))
                               (cps-of-exp body (cps-var-exp 'k%00)))))
      (zero?-exp (exp1) (cps-of-zero?-exp exp1 k-exp))
      (diff-exp (exp1 exp2) (cps-of-diff-exp exp1 exp2 k-exp))
      (sum-exp (exps) (cps-of-sum-exp exps k-exp))
      (list-exp (exps) (cps-of-list-exp exps k-exp))
      (if-exp (exp1 exp2 exp3) (cps-of-if-exp exp1 exp2 exp3 k-exp))
      (let-exp (vars rhss body) (cps-of-let-exp vars rhss body k-exp))
      (letrec-exp (p-names b-varss p-bodies letrec-body)
                  (cps-of-letrec-exp p-names b-varss p-bodies letrec-body k-exp))
      (call-exp (rator rands) (cps-of-call-exp rator rands k-exp)))))


(define cps-of-list-exp
  (lambda (exps k-exp)
    (cps-of-exps exps
                 (lambda (simples)
                   (make-send-to-cont k-exp (cps-list-exp simples))))))

; cps-of-sum-exp : Listof(InpExp) × SimpleExp → TfExp
(define cps-of-sum-exp
  (lambda (exps k-exp)
    (cps-of-exps exps
                 (lambda (simples)
                   (make-send-to-cont k-exp (cps-sum-exp simples))))))

; cps-of-simple-exp : InpExp → SimpleExp
; usage: assumes (inp-exp-simple? exp).
(define cps-of-simple-exp
  (lambda (exp)
    (cases
        expression
      exp
      (const-exp (num) (cps-const-exp num))
      (var-exp (var) (cps-var-exp var))
      (diff-exp (exp1 exp2)
                (cps-diff-exp (cps-of-simple-exp exp1) (cps-of-simple-exp exp2)))
      (zero?-exp (exp1) (cps-zero?-exp (cps-of-simple-exp exp1)))
      (proc-exp (ids exp)
                (cps-proc-exp (append ids (list 'k%00))
                              (cps-of-exp exp (cps-var-exp 'k%00))))
      (sum-exp (exps) (cps-sum-exp (map cps-of-simple-exp exps)))
      (list-exp (exps) (cps-list-exp (map cps-of-simple-exp exps)))
      (else (report-invalid-exp-to-cps-of-simple-exp exp)))))

; cps-of-call-exp : InpExp × Listof(InpExp) × SimpleExp → TfExp
(define cps-of-call-exp
  (lambda (rator rands k-exp)
    (cps-of-exps (cons rator rands)
                 (lambda (simples)
                   (cps-call-exp (car simples)
                                 (append (cdr simples) (list k-exp)))))))

; cps-of-zero?-exp : InpExp × SimpleExp → TfExp
(define cps-of-zero?-exp
  (lambda (exp1 k-exp)
    (cps-of-exps (list exp1)
                 (lambda (simples)
                   (make-send-to-cont k-exp (cps-zero?-exp (car simples)))))))

; cps-of-diff-exp : InpExp × InpExp × SimpleExp → TfExp
(define cps-of-diff-exp
  (lambda (exp1 exp2 k-exp)
    (cps-of-exps
     (list exp1 exp2)
     (lambda (simples)
       (make-send-to-cont k-exp (cps-diff-exp (car simples) (cadr simples)))))))

; cps-of-if-exp : InpExp × InpExp × InpExp × SimpleExp → TfExp
(define cps-of-if-exp
  (lambda (exp1 exp2 exp3 k-exp)
    (cps-of-exps (list exp1)
                 (lambda (simples)
                   (cps-if-exp (car simples)
                               (cps-of-exp exp2 k-exp)
                               (cps-of-exp exp3 k-exp))))))

; cps-of-let-exp : Var × InpExp × InpExp × SimpleExp → TfExp
; (define cps-of-let-exp ;;; why this fails?
;   (lambda (id rhs body k-exp)
;     (cps-of-exps (list rhs)
;                  (lambda (simples)
;                    (cps-let-exp id
;                                 (car simples)
;                                 (cps-of-exp body k-exp))))))

#|
let ids rhss 
in body

=>
(proc ids body) rhss
|#
(define cps-of-let-exp
  (lambda (ids rhss body k-exp)
    (cps-of-exp (call-exp (proc-exp ids body) rhss) k-exp)))

; cps-of-letrec-exp :
; Listof(Listof(Var)) * Listof(InpExp) * InpExp * SimpleExp -> TfExp
(define cps-of-letrec-exp
  (lambda (p-names b-varss p-bodies letrec-body k-exp)
    (cps-letrec-exp
     p-names
     (map (lambda (b-vars) (append b-vars (list 'k%00))) b-varss)
     (map (lambda (p-body) (cps-of-exp p-body (cps-var-exp 'k%00))) p-bodies)
     (cps-of-exp letrec-body k-exp))))

; cps-of-program : InpExp → TfExp
(define cps-of-program
  (lambda (pgm)
    (cases program
      pgm
      (a-program (exp1)
                 (cps-a-program
                  (cps-of-exps (list exp1)
                               (lambda (new-args) ;;; why this builder?
                                 (simple-exp->exp (car new-args)))))))))

(define transform (lambda (str) (cps-of-program (scan&parse-cps-in str))))

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
(check-equal? (value-of-cps-out-program (transform str0)) (num-val 551))

(define str1 "let f = proc(x) x
   in (f 73)")
(check-equal? (value-of-cps-out-program (transform str1)) (num-val 73))

(define str2
  "let f = proc(x) +(x, 73, 37)
   in let x = (f 21)
          y = -(12, (f 12))
      in -(x, y)")
(check-equal? (value-of-cps-out-program (transform str2)) (num-val 241))
