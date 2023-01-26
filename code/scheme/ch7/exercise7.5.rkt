#lang eopl
(require rackunit)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Grammar
(define identifier? (lambda (exp) (and (symbol? exp) (not (eqv? exp 'lambda)))))

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define the-grammar
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression)
                let-exp)
    (expression
     ("proc" "(" (separated-list identifier ":" type ",") ")" expression)
     proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression
     ("letrec"
      (arbno type identifier "("(separated-list identifier ":" type ",")")" "=" expression)
      "in"
      expression)
     letrec-exp)
    (type ("int") int-type)
    (type ("bool") bool-type)
    (type ("(" (separated-list type "*") "->" type ")") proc-type)))

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse (sllgen:make-string-parser the-lexical-spec the-grammar))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Data Type

; Environment
(define-datatype
  environment
  environment?
  (empty-env)
  (extend-env (bvar identifier?) (bval expval?) (saved-env environment?))
  (extend-env-rec (p-name identifier?)
                  (b-var identifier?)
                  (p-body expression?)
                  (saved-env environment?)))

(define-datatype proc
  proc?
  (procedure (vars (list-of identifier?))
             (body expression?)
             (saved-env environment?)))

; ExpVal
(define-datatype expval
  expval?
  (num-val (value number?))
  (bool-val (boolean boolean?))
  (proc-val (proc proc?)))

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

(define expval->scheme-val
  (lambda (v)
    (cases expval
      v
      (num-val (num) num)
      (bool-val (bool) bool)
      (proc-val (proc) proc))))

; TypeEnvironment
(define-datatype
  type-environment
  type-environment?
  (empty-tenv-record)
  (extended-tenv-record (sym identifier?) (type type?) (tenv type-environment?)))

(define empty-tenv empty-tenv-record)

(define extend-tenv extended-tenv-record)

(define extend-tenv*
  (lambda (vars types tenv)
    (if (not (= (length vars)
                (length types)))
        (eopl:error 'extend-tenv*)
        (let loop ([vars vars]
                   [types types])
          (if (null? vars)
              tenv
              (extend-tenv (car vars)
                           (car types)
                           (loop (cdr vars) (cdr types))))))))
(define apply-tenv
  (lambda (tenv sym)
    (cases
        type-environment
      tenv
      (empty-tenv-record () (eopl:error 'apply-tenv "Unbound variable ~s" sym))
      (extended-tenv-record
       (sym1 val1 old-env)
       (if (eqv? sym sym1) val1 (apply-tenv old-env sym))))))

(define init-tenv
  (lambda ()
    (extend-tenv 'true
                 (bool-type)
                 (extend-tenv 'false (bool-type) (empty-tenv)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Checker
; check-equal-type! : Type × Type × Exp → Unspecified
(define check-equal-type!
  (lambda (ty1 ty2 exp)
    (when (not (equal? ty1 ty2))
      (report-unequal-types ty1 ty2 exp))))

; report-unequal-types : Type × Type × Exp → Unspecified
(define report-unequal-types
  (lambda (ty1 ty2 exp)
    (eopl:error 'check-equal-type!
                "Types didn't match: ~s != ~a in~%~a"
                (type-to-external-form ty1)
                (type-to-external-form ty2)
                exp)))

; type-to-external-form : Type → List
(define type-to-external-form
  (lambda (ty)
    (cases type
      ty
      (int-type () 'int)
      (bool-type () 'bool)
      (proc-type
       (arg-types result-type)
       (if (null? arg-types)
           (type-to-external-form result-type)
           (let loop ([first (car arg-types)] [rest (cdr arg-types)])
             (if (null? rest)
                 (list (type-to-external-form first)
                       '->
                       (type-to-external-form result-type))
                 (cons (type-to-external-form first)
                       (cons '* (loop (car rest) (cdr rest)))))))))))

;; type-of-program : Program -> Type
(define type-of-program
  (lambda (pgm)
    (cases program pgm (a-program (exp1) (type-of exp1 (init-tenv))))))

;; type-of : Exp * Tenv -> Type
(define type-of
  (lambda (exp tenv)
    (cases
        expression
      exp
      (const-exp (num) (int-type))
      (var-exp (var) (apply-tenv tenv var))
      (diff-exp (exp1 exp2)
                (let ([ty1 (type-of exp1 tenv)] [ty2 (type-of exp2 tenv)])
                  (check-equal-type! ty1 (int-type) exp1)
                  (check-equal-type! ty2 (int-type) exp2)
                  (int-type)))
      (zero?-exp (exp1)
                 (let ([ty1 (type-of exp1 tenv)])
                   (check-equal-type! ty1 (int-type) exp1)
                   (bool-type)))
      (if-exp (exp1 exp2 exp3)
              (let ([ty1 (type-of exp1 tenv)]
                    [ty2 (type-of exp2 tenv)]
                    [ty3 (type-of exp3 tenv)])
                (check-equal-type! ty1 (bool-type) exp1)
                (check-equal-type! ty2 ty3 exp)
                ty2))
      (let-exp (vars exps body)
               (let ([types (map (lambda (exp) (type-of exp tenv)) exps)])
                 (type-of body (extend-tenv* vars types tenv))))
      (proc-exp (vars var-types body)
                (let ([result-type
                       (type-of body (extend-tenv* vars var-types tenv))])
                  (proc-type var-types result-type)))
      (call-exp
       (rator rands)
       (let ([rator-type (type-of rator tenv)]
             [rand-types (map (lambda (rand) (type-of rand tenv)) rands)])
         (cases type
           rator-type
           (proc-type (arg-types result-type)
                      (begin
                        (check-equal-type! arg-types rand-types rands)
                        result-type))
           (else (report-rator-not-a-proc-type rator-type rator)))))
      (letrec-exp
       (p-result-types p-names b-varss b-varss-types p-bodies letrec-body)
       (let ([tenv-for-letrec-body
              (extend-tenv* p-names
                            (map (lambda (b-vars-types p-result-type)
                                   (proc-type b-vars-types p-result-type))
                                 b-varss-types
                                 p-result-types) tenv
                                                 )])
         (let ([p-body-types
                (map (lambda (p-body b-vars b-vars-types)
                       (type-of p-body
                                (extend-tenv* b-vars b-vars-types tenv-for-letrec-body)))
                     p-bodies b-varss b-varss-types)])
           (check-equal-type! p-body-types p-result-types p-bodies)
           (type-of letrec-body tenv-for-letrec-body)))))))

(define report-rator-not-a-proc-type
  (lambda (rator-type rator)
    (eopl:error 'type-of-expression
                "Rator not a proc type:~%~s~%had rator type ~s"
                rator
                (type-to-external-form rator-type))))

;;; test
(define :t
  (lambda (str) (type-to-external-form (type-of-program (scan&parse str)))))

(define str0 "proc (x: int) -(x, 3)")
(check-equal? (:t str0) '(int -> int))

(define str1 "proc (f: (int -> int)) proc (x: int) -((f x), 1)")
(check-equal? (:t str1) '((int -> int) -> (int -> int)))

(define str2 "proc (x: (int -> bool)) proc (y: int) (x y)")
(check-equal? (:t str2) '((int -> bool) -> (int -> bool)))

(define str3 "proc (x: bool) if x then 88 else 99")
(check-equal? (:t str3) '(bool -> int))

(define str4 "proc (x: int) if x then 88 else 99")
; (:t str4) ; should fail

(define str5 "proc (x: bool) if x then 88 else true")
; (:t str5) ; should fail

(define str6
  "proc (f: (bool -> int))
      proc (g: (int -> int))
        proc (p: (int -> bool))
          proc (x: bool) if (p (f x)) then (g 1) else -((f x),1)")
(check-equal?
 (:t str6)
 '((bool -> int) -> ((int -> int) -> ((int -> bool) -> (bool -> int)))))

(define str7
  "proc (x: int)
      proc(p: (int -> bool))
        proc (f: ((int -> bool) -> int))
          if (p x) then -(x, 1) else (f p)")
(check-equal? (:t str7)
              '(int -> ((int -> bool) -> (((int -> bool) -> int) -> int))))

(define str8
  "letrec
     int double (x : int) = if zero?(x)
                            then 0
                            else -((double -(x,1)), -2)
   in double")
(check-equal? (:t str8) '(int -> int))

(define str9
  "proc(x: int, y: bool, z: (int * int * bool -> bool))
     if (z 10 11 true)
     then 12
     else if y
          then x
          else -(x, 1)")
(check-equal? (:t str9) '(int * bool * (int * int * bool -> bool) -> int))

(define str10 "proc() 0")
(check-equal? (:t str10) 'int)

(define str11
  "let x = 11
       y = 13
       f = proc(a: int, b: int)
             zero?(-(a, b))
       g = proc(a: int, b: int, c:(int * int -> bool))
             if (c a b) then false else true
   in (g x y f)")
(check-equal? (:t str11) 'bool)

(define str12
  " 
   letrec
     int add(a: int, b: int) = -(a, -(0, b))
     int mul(a: int, b: int) = if zero?(b) then 0 else (add a (mul a -(b, 1)))
     int fib(a: int, b: int, n: int) = if zero?(n) then b else (fib b -(a, -(0, b)) -(n, 1))
     int factk(n: int, k: (int -> int)) = if zero?(n) then (k 1) else (factk -(n, 1) proc(v0: int) (k (mul v0 n)))
   in -((factk 10 proc(x: int) x), (fib 0 1 10))")
(check-equal? (:t str12) 'int)