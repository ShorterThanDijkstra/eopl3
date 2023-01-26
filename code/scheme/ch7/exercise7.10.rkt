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
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("proc" "(" identifier ":" type ")" expression) proc-exp)
    (expression ("(" expression expression ")") call-exp)
    (expression ("letrec" type
                          identifier
                          "("
                          identifier
                          ":"
                          type
                          ")"
                          "="
                          expression
                          "in"
                          expression)
                letrec-exp)
    (expression ("newref" "(" expression ")") newref-exp)
    (expression ("deref" "(" expression ")") deref-exp)
    (expression ("setref" "(" expression "," expression ")") setref-exp)
    (type ("int") int-type)
    (type ("bool") bool-type)
    (type ("void") void-type)
    (type ("refto" type) refto-type)
    (type ("(" type "->" type ")") proc-type)))

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

(define-datatype
  proc
  proc?
  (procedure (var identifier?) (body expression?) (saved-env environment?)))

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

; TypeEnvironment
(define-datatype
  type-environment
  type-environment?
  (empty-tenv-record)
  (extended-tenv-record (sym identifier?) (type type?) (tenv type-environment?)))

(define empty-tenv empty-tenv-record)
(define extend-tenv extended-tenv-record)

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
      (void-type () 'void)
      (refto-type (ty) (list 'refto
                             (type-to-external-form ty)))
      (proc-type (arg-type result-type)
                 (list (type-to-external-form arg-type)
                       '->
                       (type-to-external-form result-type))))))

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
      (let-exp (var exp1 body)
               (let ([exp1-type (type-of exp1 tenv)])
                 (type-of body (extend-tenv var exp1-type tenv))))
      (proc-exp (var var-type body)
                (let ([result-type
                       (type-of body (extend-tenv var var-type tenv))])
                  (proc-type var-type result-type)))
      (newref-exp (exp1) (refto-type (type-of exp1 tenv)))
      (deref-exp (ref-exp) (let ([ty1 (type-of ref-exp tenv)])
                             (cases type ty1
                               (refto-type (ty2) ty2)
                               (else (eopl:error 'type-of "expect a ref type, got: ~s" ty1)))))
      (setref-exp (ref-exp val-exp) (let ([ref-ty (type-of ref-exp tenv)]
                                          [val-ty (type-of val-exp tenv)])
                                      (cases type ref-ty
                                        (refto-type (ty1)
                                                    (check-equal-type! ty1 val-ty val-exp)
                                                    (void-type))
                                        (else (eopl:error 'type-of "expect a ref type, got: ~s" ref-ty)))))
      (call-exp
       (rator rand)
       (let ([rator-type (type-of rator tenv)] [rand-type (type-of rand tenv)])
         (cases type
           rator-type
           (proc-type (arg-type result-type)
                      (begin
                        (check-equal-type! arg-type rand-type rand)
                        result-type))
           (else (report-rator-not-a-proc-type rator-type rator)))))
      (letrec-exp
       (p-result-type p-name b-var b-var-type p-body letrec-body)
       (let ([tenv-for-letrec-body
              (extend-tenv p-name (proc-type b-var-type p-result-type) tenv)])
         (let ([p-body-type
                (type-of p-body
                         (extend-tenv b-var b-var-type tenv-for-letrec-body))])
           (check-equal-type! p-body-type p-result-type p-body)
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
  "let x = newref(22)
   in let f = proc (z: refto int) let zz = newref(-(deref(z), deref(x)))
                       in deref(zz)
      in -((f newref(66)), (f newref(55)))")
(check-equal? (:t str9) 'int)

(define str10
  "let x = newref(11)
   in setref(x, 13)")
(check-equal? (:t str10) 'void)