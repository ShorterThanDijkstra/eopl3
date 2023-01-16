#lang eopl
(require rackunit)
(require racket/format)

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
           (procedure (vars body saved-env)
                      (value-of/k body
                                  (extend-env* vars (map newref args) saved-env)
                                  cont)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal data type
(define-datatype expval
                 expval?
                 (num-val (value number?))
                 (bool-val (boolean boolean?))
                 (proc-val (proc proc?))
                 (ref-val (val reference?)))

(define expval->num
  (lambda (v) (cases expval v (num-val (num) num) (else (eopl:error)))))

(define expval->bool
  (lambda (v) (cases expval v (bool-val (bool) bool) (else (eopl:error)))))

(define expval->proc
  (lambda (v) (cases expval v (proc-val (proc) proc) (else (eopl:error)))))

(define expval->ref
  (lambda (v)
    (cases expval
           v
           (ref-val (ref) ref)
           (else ((eopl:error 'expval->ref "~s" v))))))

(define expval->scheme-val
  (lambda (v)
    (cases expval
           v
           (num-val (num) num)
           (bool-val (bool) bool)
           (proc-val (proc) proc)
           (ref-val (ref) ref))))

(define expval->string
  (lambda (v)
    (cases expval
           v
           (num-val (num) (number->string num))
           (bool-val (bool) (~a bool))
           (proc-val (proc) "<procedure>")
           (ref-val (ref) "<ref>"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Store
(define empty-store (lambda () '()))

(define the-store 'uninitialized)

(define get-store (lambda () the-store))

(define initialize-store! (lambda () (set! the-store (empty-store))))

(define reference? (lambda (v) (integer? v)))

(define newref
  (lambda (val)
    (let ([next-ref (length the-store)])
      (set! the-store (append the-store (list val)))
      next-ref)))

(define deref (lambda (ref) (list-ref the-store ref)))

(define setref!
  (lambda (ref val)
    (set!
     the-store
     (letrec ([setref-inner
               (lambda (store1 ref1)
                 (cond
                   [(null? store1)
                    (eopl:error "report-invalid-reference ~s" ref the-store)]
                   [(zero? ref1) (cons val (cdr store1))]
                   [else
                    (cons (car store1)
                          (setref-inner (cdr store1) (- ref1 1)))]))])
       (setref-inner the-store ref)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Env
(define-datatype
 environment
 environment?
 (empty-env)
 (extend-env (var identifier?) (ref reference?) (env environment?))
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
     (extend-env (saved-var saved-ref saved-env)
                 (if (eqv? saved-var search-var)
                     saved-ref
                     (apply-env saved-env search-var)))
     (extend-env-rec**
      (p-names b-varss p-bodies saved-env)
      (let search ([p-names p-names] [b-varss b-varss] [p-bodies p-bodies])
        (if (null? p-names)
            (apply-env saved-env search-var)
            (if (eqv? (car p-names) search-var)
                (newref (proc-val (procedure (car b-varss) (car p-bodies) env)))
                (search (cdr p-names) (cdr b-varss) (cdr p-bodies)))))))))

(define extend-env*
  (lambda (vars refs env)
    (if (null? vars)
        env
        (extend-env (car vars)
                    (car refs)
                    (extend-env* (cdr vars) (cdr refs) env)))))

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
    (tfexp (simple-expression) simple-exp->exp)
    (tfexp ("let" identifier "=" simple-expression "in" tfexp) cps-let-exp)
    (tfexp ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" tfexp)
                     "in"
                     tfexp)
           cps-letrec-exp)
    (tfexp ("if" simple-expression "then" tfexp "else" tfexp) cps-if-exp)
    (tfexp ("print" "(" simple-expression ")" ";" tfexp) cps-print-exp)
    (tfexp ("newref" "(" simple-expression "," simple-expression ")")
           cps-newref-exp)
    (tfexp ("deref" "(" simple-expression "," simple-expression ")")
           cps-deref-exp)
    (tfexp ("setref" "(" simple-expression "," simple-expression ")" ";" tfexp)
           cps-setref-exp)
    (tfexp ("(" simple-expression (arbno simple-expression) ")") cps-call-exp)))

(define scan&parse
  (sllgen:make-string-parser cps-out-lexical-spec cps-out-grammar-spec))

(sllgen:make-define-datatypes cps-out-lexical-spec cps-out-grammar-spec)

(define list-the-datatypes
  (lambda ()
    (sllgen:list-define-datatypes cps-out-lexical-spec cps-out-grammar-spec)))

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
     (cps-var-exp (var) (deref (apply-env env var)))
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
     (cps-let-exp (var rhs body)
                  (let ([val (value-of-simple-exp rhs env)])
                    (value-of/k body (extend-env var (newref val) env) cont)))
     (cps-letrec-exp (p-names b-varss p-bodies letrec-body)
                     (value-of/k letrec-body
                                 (extend-env-rec** p-names b-varss p-bodies env)
                                 cont))
     (cps-if-exp (simple1 body1 body2)
                 (if (expval->bool (value-of-simple-exp simple1 env))
                     (value-of/k body1 env cont)
                     (value-of/k body2 env cont)))
     (cps-print-exp (simple body)
                    (begin
                      (display (expval->string
                                (value-of-simple-exp simple env)))
                      (newline)
                      (value-of/k body env cont)))
     (cps-newref-exp
      (simple1 simple2)
      (let ([val1 (value-of-simple-exp simple1 env)]
            [val2 (value-of-simple-exp simple2 env)])
        (let ([newval (ref-val (newref val1))])
          (apply-procedure/k (expval->proc val2) (list newval) cont))))
     (cps-deref-exp
      (simple1 simple2)
      (apply-procedure/k
       (expval->proc (value-of-simple-exp simple2 env))
       (list (deref (expval->ref (value-of-simple-exp simple1 env))))
       cont))
     (cps-setref-exp (simple1 simple2 body)
                     (let ([ref (expval->ref (value-of-simple-exp simple1 env))]
                           [val (value-of-simple-exp simple2 env)])
                       (begin
                         (setref! ref val)
                         (value-of/k body env cont))))
     (cps-call-exp
      (rator rands)
      (let ([rator-proc (expval->proc (value-of-simple-exp rator env))]
            [rand-vals
             (map (lambda (simple) (value-of-simple-exp simple env)) rands)])
        (apply-procedure/k rator-proc rand-vals cont))))))

(define init-env
  (lambda ()
    (extend-env 'true
                (newref (bool-val #t))
                (extend-env 'false (newref (bool-val #f)) (empty-env)))))

(define value-of-program
  (lambda (pgm)
    (initialize-store!)
    (cases cps-out-program
           pgm
           (cps-a-program (exp1) (value-of/k exp1 (init-env) (end-cont))))))

(define run (lambda (code) (value-of-program (scan&parse code))))

(define value-of-cps-out-program value-of-program)

; (provide value-of-cps-out-program
;          cps-out-program
;          cps-out-program?
;          cps-a-program
;          simple-expression
;          simple-expression?
;          cps-const-exp
;          cps-var-exp
;          cps-diff-exp
;          cps-zero?-exp
;          cps-sum-exp
;          cps-proc-exp
;          tfexp
;          tfexp?
;          simple-exp->exp
;          cps-let-exp
;          cps-letrec-exp
;          cps-if-exp
;          cps-print-exp
;          cps-newref-exp
;          cps-deref-exp
;          cps-setref-exp
;          cps-call-exp)
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;test
(define str0
  "
  letrec double(x k)
          = if zero?(x) then (k 0) else (double -(x, 1) proc(v0) (k -(v0, -2)))
  in (double 7 proc(x) x)
   ")
(check-equal? (run str0) (num-val 14))
(define str2
  "
  let not = proc(b k) if b then (k false) else (k true)
  in letrec even?(n k) =  if zero?(n)
                          then (k true)
                          else let m = -(n, 1)
                               in print(m);
                                  (even? m proc(b) (not b k))
     in (even? 11 proc(x) print (x); x)
  ")
; (check-equal? (run str2) (bool-val #f)) ; works

#|
let loc1 = newref(33)
in let loc2 = newref(44)
   in let void = setref(loc1, 22)
      in -(deref(loc1), 1)
|#
(define str3
  "newref(33, proc (loc1)
                newref(44, proc (loc2)
                              setref(loc1, 22);
                              deref(loc1, proc (val)
                                            -(val,1))))")
; (check-equal? (run str3) (num-val 21)) ; works
