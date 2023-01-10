#lang eopl
(require rackunit)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Procedure data type
(define-datatype proc
  proc?
  (procedure (vars (list-of identifier?))
             (body TfExp?)
             (saved-env environment?)))

; apply-procedure : Proc × ExpVal → ExpVal
(define apply-procedure/k
  (lambda (proc1 args)
    (cases proc
      proc1
      (procedure
       (vars body saved-env)
       (value-of/k body (extend-env* vars args saved-env))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal data type
(define-datatype expval
  expval?
  (num-val (value number?))
  (bool-val (boolean boolean?))
  (proc-val (proc proc?))
  (pair-val (fst expval?) (snd expval?))
  (nil-val))

(define expval->num
  (lambda (v)
    (cases expval
      v
      (num-val (num) num)
      (else (eopl:error 'expval->num "~s" v)))))


(define num-val?
  (lambda (v)
    (cases expval
      v
      (num-val (_) #t)
      (else #f))))

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

(define expval->pair-fst
  (lambda (v)
    (cases expval
      v
      (pair-val (fst snd) fst)
      (else (eopl:error 'expval->pair-fst "~s" v)))))

(define expval->pair-snd
  (lambda (v)
    (cases expval
      v
      (pair-val (fst snd) snd)
      (else (eopl:error 'expval->pair-snd "~s" v)))))

(define expval->nil
  (lambda (v)
    (cases expval v (nil-val () 'nil) (else (eopl:error 'expval->nil "~s" v)))))

(define nil? (lambda (v) (cases expval v (nil-val () #t) (else #f))))

(define pair-val?
  (lambda (v) (cases expval v (pair-val (fst snd) #t) (else #f))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Env
(define-datatype environment
  environment?
  (empty-env)
  (extend-env (var identifier?) (val expval?) (env environment?))
  (extend-env-rec** (p-names (list-of identifier?))
                    (b-varss (list-of (list-of identifier?)))
                    (bodies (list-of TfExp?))
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
  '((CpsProgram (TfExp) a-cps-program)
    (SimpleExp (number) cps-const-exp)
    (SimpleExp (identifier) cps-var-exp)
    (SimpleExp ("-" "(" SimpleExp "," SimpleExp ")") cps-diff-exp)
    (SimpleExp ("*" "(" SimpleExp "," SimpleExp ")") cps-mul-exp)
    (SimpleExp ("zero?" "(" SimpleExp ")") cps-zero?-exp)
    (SimpleExp ("add1" "(" SimpleExp ")") cps-add1-exp)
    (SimpleExp ("proc" "(" (separated-list identifier ",") ")" TfExp) cps-proc-exp)
    (SimpleExp ("emptylist") cps-nil-exp)
    (SimpleExp ("car" "(" SimpleExp ")" ) cps-car-exp)
    (SimpleExp ("cdr" "(" SimpleExp ")" ) cps-cdr-exp)
    (SimpleExp ("null?" "(" SimpleExp ")" ) cps-null?-exp)
    (SimpleExp ("cons" "(" SimpleExp "," SimpleExp ")") cps-cons-exp)
    (SimpleExp ("list" "(" (separated-list SimpleExp ",") ")") cps-list-exp)
    (SimpleExp ("number?" "(" SimpleExp ")") cps-number?-exp)
    (SimpleExp ("equal?" "(" SimpleExp "," SimpleExp ")") cps-equal?-exp)
    (SimpleExp ("less?" "(" SimpleExp "," SimpleExp ")") cps-less?-exp)
    (SimpleExp ("greater?" "(" SimpleExp "," SimpleExp ")") cps-greater?-exp)
    (TfExp     (SimpleExp) simple-exp->exp)
    (TfExp     ("let" identifier "=" SimpleExp "in" TfExp) cps-let-exp)
    (TfExp     ("letrec"
                (arbno identifier "(" (separated-list identifier ",") ")" "=" TfExp)
                "in"
                TfExp)
               cps-letrec-exp)
    (TfExp     ("if" SimpleExp "then" TfExp "else" TfExp) cps-if-exp)
    (TfExp     ("(" SimpleExp (arbno SimpleExp) ")") cps-call-exp)))

(define list-cps-out-datatypes
  (lambda ()
    (sllgen:list-define-datatypes cps-out-lexical-spec cps-out-grammar-spec)))

(define scan&parse
  (sllgen:make-string-parser cps-out-lexical-spec cps-out-grammar-spec))

(sllgen:make-define-datatypes cps-out-lexical-spec cps-out-grammar-spec)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter
(define value-of-simple-exp
  (lambda (simple env)
    (cases
        SimpleExp
      simple
      (cps-const-exp (num) (num-val num))
      (cps-var-exp (var) (apply-env env var))
      (cps-diff-exp (exp1 exp2)
                    (let ([val1 (value-of-simple-exp exp1 env)]
                          [val2 (value-of-simple-exp exp2 env)])
                      (let ([num1 (expval->num val1)] [num2 (expval->num val2)])
                        (num-val (- num1 num2)))))
      (cps-mul-exp (exp1 exp2)
                   (let ([val1 (value-of-simple-exp exp1 env)]
                         [val2 (value-of-simple-exp exp2 env)])
                     (let ([num1 (expval->num val1)] [num2 (expval->num val2)])
                       (num-val (* num1 num2)))))
      (cps-zero?-exp (exp1)
                     (let ([val1 (value-of-simple-exp exp1 env)])
                       (let ([num1 (expval->num val1)])
                         (if (zero? num1) (bool-val #t) (bool-val #f)))))
      (cps-add1-exp (exp1)
                    (let ([val1 (value-of-simple-exp exp1 env)])
                      (let ([num1 (expval->num val1)])
                        (num-val (+ num1 1)))))
      (cps-proc-exp (vars body) (proc-val (procedure vars body env)))
      (cps-nil-exp () (nil-val))
      (cps-car-exp (exp1)
                   (let ((pair (value-of-simple-exp exp1 env)))
                     (expval->pair-fst pair)))
      (cps-cdr-exp (exp1)
                   (let ((pair (value-of-simple-exp exp1 env)))
                     (expval->pair-snd pair)))
      (cps-null?-exp (exp1)
                     (let ((val (value-of-simple-exp exp1 env)))
                       (bool-val (nil? val))))
      (cps-cons-exp (exp1 exp2)
                    (let ((fst (value-of-simple-exp exp1 env))
                          (snd (value-of-simple-exp exp2 env)))
                      (pair-val fst snd)))
      (cps-list-exp (exps)
                    (let loop ((vals (map (lambda(exp) (value-of-simple-exp exp env)) exps)))
                      (if (null? vals)
                          (nil-val)
                          (pair-val (car vals)
                                    (loop (cdr vals))))))
      (cps-number?-exp (exp1)
                       (bool-val (num-val? (value-of-simple-exp exp1 env))))
      (cps-equal?-exp (exp1 exp2)
                      (let ((val1 (value-of-simple-exp exp1 env))
                            (val2 (value-of-simple-exp exp2 env)))
                        (bool-val (= (expval->num val1) (expval->num val2)))))
      (cps-less?-exp (exp1 exp2)
                     (let ((val1 (value-of-simple-exp exp1 env))
                           (val2 (value-of-simple-exp exp2 env)))
                       (bool-val (< (expval->num val1) (expval->num val2)))))
      (cps-greater?-exp (exp1 exp2)
                        (let ((val1 (value-of-simple-exp exp1 env))
                              (val2 (value-of-simple-exp exp2 env)))
                          (bool-val (> (expval->num val1) (expval->num val2)))))
      )))

; value-of/k : TfExp × Env → FinalAnswer
(define value-of/k
  (lambda (exp env)
    (cases
        TfExp
      exp
      (simple-exp->exp (simple)
                       (value-of-simple-exp simple env))
      (cps-let-exp
       (var rhs body)
       (let ([val (value-of-simple-exp rhs env)])
         (value-of/k body (extend-env var val env))))
      (cps-letrec-exp (p-names b-varss p-bodies letrec-body)
                      (value-of/k letrec-body
                                  (extend-env-rec** p-names b-varss p-bodies env)))
      (cps-if-exp (simple1 body1 body2)
                  (if (expval->bool (value-of-simple-exp simple1 env))
                      (value-of/k body1 env )
                      (value-of/k body2 env )))
      (cps-call-exp
       (rator rands)
       (let ([rator-proc (expval->proc (value-of-simple-exp rator env))]
             [rand-vals
              (map (lambda (simple) (value-of-simple-exp simple env)) rands)])
         (apply-procedure/k rator-proc rand-vals))))))

(define init-env
  (lambda ()
    (extend-env 'true
                (bool-val #t)
                (extend-env 'false (bool-val #f) (empty-env)))))

(define value-of-program
  (lambda (pgm)
    (cases CpsProgram
      pgm
      (a-cps-program (exp1) (value-of/k exp1 (init-env))))))

(define run (lambda (code) (value-of-program (scan&parse code))))


(define str0
  "
  letrec double(x, k)
          = if zero?(x) then (k 0) else (double -(x, 1) proc(v0) (k -(v0, -2)))
  in (double 17 proc(x) x)
   ")
(check-equal? (run str0) (num-val 34))

(define removeall
  "letrec removeall(n, s, k) =
       if null?(s)
       then (k emptylist)
       else if number?(car(s))
            then if equal?(n, car(s))
                    then (removeall n cdr(s) k)
                    else (removeall n cdr(s) proc(v0) (k cons(car(s), v0)))
            else (removeall n car(s) proc(v0) (removeall n cdr(s) proc(v1) (k cons(v0, v1))))
  in let s = cons(7, cons(cons(29, cons(3, emptylist)), cons(3, cons(73, cons(3, emptylist)))))
      in (removeall 3 s proc(x) x)")
(check-equal? (run removeall)  (pair-val
                                (num-val 7)
                                (pair-val
                                 (pair-val (num-val 29) (nil-val))
                                 (pair-val (num-val 73) (nil-val)))))

(define occurs-in0?
  "letrec occurs-in?(n, s, k) =
          if null?(s)
          then (k 0)
          else if number?(car(s))
               then if equal?(n, car(s))
                    then (k 1)
                    else (occurs-in? n cdr(s) k)
               else (occurs-in? n car(s) k
                                proc(v0) if v0
                                         then (k 1)
                                         else (occurs-in? n cdr(s) k))
    in let s = cons(7, cons(cons(29, cons(31, emptylist)), cons(3, cons(73, cons(3, emptylist)))))
       in (occurs-in? 31 s proc(x) x)")
(check-equal? (run occurs-in0?)  (num-val 1))

(define occurs-in1?
  "letrec occurs-in?(n, s, k) =
          if null?(s)
          then (k 0)
          else if number?(car(s))
               then if equal?(n, car(s))
                    then (k 1)
                    else (occurs-in? n cdr(s) k)
               else (occurs-in? n car(s) k
                                proc(v0) if v0
                                         then (k 1)
                                         else (occurs-in? n cdr(s) k))
    in let s = cons(7, cons(cons(29, cons(31, emptylist)), cons(3, cons(73, cons(3, emptylist)))))
       in (occurs-in? 83 s proc(x) x)")
(check-equal? (run occurs-in1?) (num-val 0))

(define remfirst
  "letrec occurs-in?(n, s, k) =
          if null?(s)
          then (k false)
          else if number?(car(s))
               then if equal?(n, car(s))
                    then (k true)
                    else (occurs-in? n cdr(s) k)
               else (occurs-in? n car(s) k
                                proc(v0) if v0
                                         then (k 1)
                                         else (occurs-in? n cdr(s) k))
    in letrec remfirst(n, s, k) =
              letrec loop(s, k) =
                     if null?(s)
                     then (k emptylist)
                     else if number?(car(s))
                          then if equal?(n,car(s))
                               then (k cdr(s))
                               else (loop cdr(s) proc(v0) (k cons(car(s), v0)))
                          else (occurs-in? n car(s)
                                           proc(v0) if v0
                                                    then
                                                    (remfirst n car(s)
                                                              proc(v0) (k cons(v0, cdr(s))))
                                                    else (remfirst n cdr(s)
                                                                   proc(v0) (k cons(car(s), v0))))
              in (loop s k)
        in let s = cons(7, cons(cons(29, cons(31, emptylist)), cons(3, cons(73, cons(3, emptylist)))))
           in (remfirst 31 s proc(x) x)")

(check-equal? (run remfirst) (pair-val
                              (num-val 7)
                              (pair-val
                               (pair-val (num-val 29) (nil-val))
                               (pair-val
                                (num-val 3)
                                (pair-val (num-val 73) (pair-val (num-val 3) (nil-val)))))))

(define depth
  "letrec depth(s, k) =
          if null?(s)
          then (k 1)
          else if number?(car(s))
               then (depth cdr(s) k)
               else (depth car(s)
                           proc(v0) (depth cdr(s)
                                           proc(v1) if less?(add1(v0), v1)
                                                    then (depth cdr(s) k)
                                                    else (depth car(s) proc(v2) (k add1(v2)))))
  in let s = cons(7, cons(cons(29, cons(31, emptylist)), cons(3, cons(73, cons(3, emptylist)))))
     in (depth s proc(x) x)")
(check-equal? (run depth) (num-val 2))

(define depth-with-let
  "letrec depth(s, k) =
          if null?(s)
          then (k 1)
          else if number?(car(s))
               then (depth cdr(s) k)
               else (depth car(s)
                      proc(v0) let dfirst = add1(v0)
                               in (depth cdr(s)
                                         proc(v1) let drest = v1
                                                  in if less?(dfirst, drest)
                                                     then (k drest)
                                                     else (k dfirst)))
  in let s = cons(7, cons(cons(29, cons(31, emptylist)), cons(3, cons(73, cons(3, emptylist)))))
     in (depth s proc(x) x)")
(check-equal? (run depth-with-let) (num-val 2))

(define map-str
  "letrec map(f, l, k) =
            if null?(l)
            then (k emptylist)
            else (f car(l)
                    proc(v0) (map f cdr(l)
                                  proc(v1) (k cons(v0, v1))))
          square(n, k) = (k *(n,n))
   in (map square list(1,2,3,4,5) proc(x) x)")
(check-equal? (run map-str) (run "list(1,4,9,16,25)"))

(define fnlrgtn
  "letrec fnlrgtn(s, n, k) =
          if null?(s)
          then (k s)
          else if number?(car(s))
               then if less?(n, car(s))
                    then (k car(s))
                    else (fnlrgtn cdr(s) n k)
               else (fnlrgtn car(s) n
                             proc(v0) if null?(v0)
                                      then (fnlrgtn cdr(s) n k)
                                      else (k v0))
  in let s = list(1,list(3,list(2),7,list(9)))
     in (fnlrgtn s 6 proc(x) x)")
(check-equal? (run fnlrgtn) (num-val 7))

(define every
  "letrec every(pred, l, k) =
            if null?(l)
            then (k 1)
            else (pred car(l)
                       proc(v0) if v0
                                then (every pred cdr(l) k)
                                else (k 0))
   in let pred1 = proc(n, k) (k greater?(n,5))
      in (every pred1 list(6,7,8,9) proc(x) x)")
(check-equal? (run every) (num-val 1))
