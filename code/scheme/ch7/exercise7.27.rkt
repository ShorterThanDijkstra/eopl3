#lang eopl
(require rackunit)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;  Language
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
    (expression ("proc" "(" identifier ":" optional-type ")" expression)
                proc-exp)
    (expression ("(" expression expression ")") call-exp)
    (expression ("letrec" optional-type
                          identifier
                          "("
                          identifier
                          ":"
                          optional-type
                          ")"
                          "="
                          expression
                          "in"
                          expression)
                letrec-exp)
    (optional-type ("?") no-type)
    (optional-type (type) a-type)
    (type ("int") int-type)
    (type ("bool") bool-type)
    (type ("(" type "->" type ")") proc-type)
    (type ("%tvar-type" number) tvar-type)))

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse (sllgen:make-string-parser the-lexical-spec the-grammar))

(define proc-type?
  (lambda (ty) (cases type ty [proc-type (t1 t2) #t] [else #f])))

(define tvar-type?
  (lambda (ty) (cases type ty [tvar-type (serial-number) #t] [else #f])))

(define proc-type->arg-type
  (lambda (ty)
    (cases type
           ty
           [proc-type (arg-type result-type) arg-type]
           [else (eopl:error 'proc-type->arg-type "Not a proc type: ~s" ty)])))

(define proc-type->result-type
  (lambda (ty)
    (cases
     type
     ty
     [proc-type (arg-type result-type) result-type]
     [else (eopl:error 'proc-type->result-types "Not a proc type: ~s" ty)])))

; optype->type : OptionalType → Type
(define otype->type
  (lambda (otype)
    (cases optional-type
           otype
           (no-type () (fresh-tvar-type))
           (a-type (ty) ty))))

; fresh-tvar-type : () → Type
(define fresh-tvar-type
  (let ([sn 0])
    (lambda ()
      (set! sn (+ sn 1))
      (tvar-type sn))))

(define type-to-external-form
  (lambda (ty)
    (cases type
           ty
           (int-type () 'int)
           (bool-type () 'bool)
           (proc-type (arg-type result-type)
                      (list (type-to-external-form arg-type)
                            '->
                            (type-to-external-form result-type)))
           (tvar-type
            (serial-number)
            (string->symbol
             (string-append "tvar" (number->string serial-number)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;  Substitutions
; apply-one-subst : Type × Tvar × Type → Type
; ty0: old
; ty1: new
(define apply-one-subst
  (lambda (ty0 tvar ty1)
    (cases type
           ty0
           (int-type () (int-type))
           (bool-type () (bool-type))
           (proc-type (arg-type result-type)
                      (proc-type (apply-one-subst arg-type tvar ty1)
                                 (apply-one-subst result-type tvar ty1)))
           (tvar-type (sn) (if (equal? ty0 tvar) ty1 ty0)))))

; apply-subst-to-type : Type × Subst → Type
(define apply-subst-to-type
  (lambda (ty subst)
    (cases
     type
     ty
     (int-type () (int-type))
     (bool-type () (bool-type))
     (proc-type (t1 t2)
                (proc-type (apply-subst-to-type t1 subst)
                           (apply-subst-to-type t2 subst)))
     (tvar-type (sn) (let ([tmp (assoc ty subst)]) (if tmp (cdr tmp) ty))))))

; empty-subst : () → Subst
(define empty-subst (lambda () '()))

(define empty-subst? null?)

(define pair-of
  (lambda (pred1 pred2)
    (lambda (val) (and (pair? val) (pred1 (car val)) (pred2 (cdr val))))))

(define substitution? (list-of (pair-of tvar-type? type?)))

; extend-subst : Subst × Tvar × Type → Subst
; usage: tvar not already bound in subst.
(define extend-subst
  (lambda (subst tvar ty)
    (cons (cons tvar ty)
          (map (lambda (p)
                 (let ([oldlhs (car p)] [oldrhs (cdr p)])
                   (cons oldlhs (apply-one-subst oldrhs tvar ty))))
               subst))))

(define subst-fst (lambda (subst) (car subst)))

(define subst-rest (lambda (subst) (cdr subst)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;  Unifier
; unifier : Type × Type × Subst × Exp → Subst
(define unifier
  (lambda (ty1 ty2 subst exp)
    (let ([ty1 (apply-subst-to-type ty1 subst)]
          [ty2 (apply-subst-to-type ty2 subst)])
      (cond
        [(equal? ty1 ty2) subst]
        [(tvar-type? ty1)
         (if (no-occurrence? ty1 ty2)
             (extend-subst subst ty1 ty2)
             (report-no-occurrence-violation ty1 ty2 exp))]
        [(tvar-type? ty2)
         (if (no-occurrence? ty2 ty1)
             (extend-subst subst ty2 ty1)
             (report-no-occurrence-violation ty2 ty1 exp))]
        [(and (proc-type? ty1) (proc-type? ty2))
         (let ([subst (unifier (proc-type->arg-type ty1)
                               (proc-type->arg-type ty2)
                               subst
                               exp)])
           (let ([subst (unifier (proc-type->result-type ty1)
                                 (proc-type->result-type ty2)
                                 subst
                                 exp)])
             subst))]
        [else (report-unification-failure ty1 ty2 exp)]))))

; no-occurrence? : Tvar × Type → Bool
(define no-occurrence?
  (lambda (tvar ty)
    (cases type
           ty
           (int-type () #t)
           (bool-type () #t)
           (proc-type (arg-type result-type)
                      (and (no-occurrence? tvar arg-type)
                           (no-occurrence? tvar result-type)))
           (tvar-type (serial-number) (not (equal? tvar ty))))))

(define report-unification-failure
  (lambda (ty1 ty2 exp)
    (eopl:error 'unification-failure
                "Type mismatch: ~s doesn't match ~s in ~s~%"
                (type-to-external-form ty1)
                (type-to-external-form ty2)
                exp)))

(define report-no-occurrence-violation
  (lambda (ty1 ty2 exp)
    (eopl:error
     'check-no-occurence!
     "Can't unify: type variable ~s occurs in type ~s in expression ~s~%"
     (type-to-external-form ty1)
     (type-to-external-form ty2)
     exp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;  Type Environment
(define-datatype
 type-environment
 type-environment?
 (empty-tenv-record)
 (extended-tenv-record (sym symbol?) (type type?) (tenv type-environment?)))

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
;;;  Inferrer
;; Answer = Type * Subst
(define-datatype answer answer? (an-answer (type type?) (subst substitution?)))

;; type-of-program : Program -> Type
(define type-of-program
  (lambda (pgm)
    (cases program
           pgm
           (a-program
            (exp1)
            (let ([subst (gen-subst exp1 (init-tenv) (empty-subst))])
              (let ([fst (subst-fst subst)])
                ;  (for-each (lambda (record)
                ;              (display (car record))
                ;              (display " == ")
                ;              (display (cdr record))
                ;              (newline))
                ;            subst)
                ;  (display "------------------------")
                ;  (newline)
                ;  (display (car fst))
                ;  (newline)
                ;  (display (cdr fst))
                ;  (newline)
                ;  (display "------------------------")
                ;  (newline)
                (apply-subst-to-type (car fst) (unify subst exp1))))))))

(define unify
  (lambda (subst exp)
    (if (null? subst)
        (empty-subst)
        (let ([fst (subst-fst subst)] [rest (subst-rest subst)])
          (unifier (car fst) (cdr fst) (unify rest exp) exp)))))

; gen-subst : Expression × Tenv × Subst -> Subst
(define gen-subst
  (lambda (exp tenv subst)
    (cases
     expression
     exp
     (const-exp (num)
                (let ([tvar1 (fresh-tvar-type)])
                  (extend-subst subst tvar1 (int-type))))
     (zero?-exp (exp1)
                (let ([subst (gen-subst exp1 tenv subst)])
                  (let ([exp1-tvar (car (subst-fst subst))])
                    (let ([subst (extend-subst subst exp1-tvar (int-type))]
                          [tvar1 (fresh-tvar-type)])
                      (extend-subst subst tvar1 (bool-type))))))
     (diff-exp
      (exp1 exp2)
      (let* ([subst (gen-subst exp1 tenv subst)]
             [exp1-tvar (car (subst-fst subst))])
        (let* ([subst
                (gen-subst exp2 tenv (extend-subst subst exp1-tvar (int-type)))]
               [exp2-tvar (car (subst-fst subst))])
          (let ([tvar (fresh-tvar-type)]
                [subst (extend-subst subst exp2-tvar (int-type))])
            (extend-subst subst tvar (int-type))))))
     (if-exp (exp1 exp2 exp3)
             (let* ([subst (gen-subst exp1 tenv subst)]
                    [exp1-tvar (car (subst-fst subst))])
               (let* ([subst (gen-subst
                              exp2
                              tenv
                              (extend-subst subst exp1-tvar (bool-type)))]
                      [exp2-tvar (car (subst-fst subst))])
                 (let* ([subst (gen-subst exp3 tenv subst)]
                        [exp3-tvar (car (subst-fst subst))])
                   (extend-subst subst exp2-tvar exp3-tvar)))))
     (var-exp (var)
              (extend-subst subst
                            (fresh-tvar-type)
                            (apply-subst-to-type (apply-tenv tenv var) subst)))
     (let-exp (var exp1 body)
              (let* ([subst (gen-subst exp1 tenv subst)]
                     [exp1-tvar (car (subst-fst subst))])
                (gen-subst body (extend-tenv var exp1-tvar tenv) subst)))
     (proc-exp
      (var otype body)
      (let ([arg-type (otype->type otype)])
        (let ([subst (gen-subst body (extend-tenv var arg-type tenv) subst)])
          (let ([body-tvar (car (subst-fst subst))] [tvar (fresh-tvar-type)])
            (extend-subst subst tvar (proc-type arg-type body-tvar))))))
     (call-exp
      (rator rand)
      (let ([subst (gen-subst rator tenv subst)])
        (let ([rator-tvar (car (subst-fst subst))])
          (let ([subst (gen-subst rand tenv subst)])
            (let ([rand-tvar (car (subst-fst subst))])
              (let ([tvar (fresh-tvar-type)])
                (extend-subst
                 (extend-subst subst rator-tvar (proc-type rand-tvar tvar))
                 tvar
                 tvar)))))))
     (letrec-exp
      (proc-result-otype proc-name bvar proc-arg-otype proc-body letrec-body)
      (let ([proc-arg-type (otype->type proc-arg-otype)]
            [proc-result-type (otype->type proc-result-otype)])
        (let ([tenv-for-letrec-body
               (extend-tenv proc-name
                            (proc-type proc-arg-type proc-result-type)
                            tenv)])
          (let ([subst (gen-subst
                        proc-body
                        (extend-tenv bvar proc-arg-type tenv-for-letrec-body)
                        subst)])
            (let ([proc-body-tvar (car (subst-fst subst))])
              (let ([subst
                     (extend-subst subst proc-body-tvar proc-result-type)])
                (gen-subst letrec-body tenv-for-letrec-body subst))))))))))

; TvarTypeSym = a symbol ending with a digit
; A-list = Listof(Pair(TvarTypeSym, TvarTypeSym))
; equal-up-to-gensyms? : S-exp × S-exp → Bool
(define equal-up-to-gensyms?
  (lambda (sexp1 sexp2)
    (equal? (apply-subst-to-sexp (canonical-subst sexp1) sexp1)
            (apply-subst-to-sexp (canonical-subst sexp2) sexp2))))

; canonical-subst : S-exp → A-list
(define canonical-subst
  (lambda (sexp)
    ; loop : S-exp × A-list → A-list
    (let loop ([sexp sexp] [table '()])
      (cond
        [(null? sexp) table]
        [(tvar-type-sym? sexp)
         (cond
           [(assq sexp table) table]
           [else (cons (cons sexp (ctr->ty (length table))) table)])]
        [(pair? sexp) (loop (cdr sexp) (loop (car sexp) table))]
        [else table]))))

; tvar-type-sym? : Sym → Bool
(define tvar-type-sym?
  (lambda (sym)
    (and (symbol? sym) (char-numeric? (car (reverse (symbol->list sym)))))))

; symbol->list : Sym → List
(define symbol->list (lambda (x) (string->list (symbol->string x))))

; apply-subst-to-sexp : A-list × S-exp → S-exp
(define apply-subst-to-sexp
  (lambda (subst sexp)
    (cond
      [(null? sexp) sexp]
      [(tvar-type-sym? sexp) (cdr (assq sexp subst))]
      [(pair? sexp)
       (cons (apply-subst-to-sexp subst (car sexp))
             (apply-subst-to-sexp subst (cdr sexp)))]
      [else sexp])))

; ctr->ty : N → Sym
(define ctr->ty
  (lambda (n) (string->symbol (string-append "tvar" (number->string n)))))

;;; test
(define type-eq?
  (lambda (str expected)
    (check-true (equal-up-to-gensyms?
                 (type-to-external-form (type-of-program (scan&parse str)))
                 expected))))

(define type-not-eq?
  (lambda (str expected)
    (check-false (equal-up-to-gensyms?
                  (type-to-external-form (type-of-program (scan&parse str)))
                  expected))))
(define :t
  (lambda (str)
    (let ([ty-sexp (type-to-external-form (type-of-program (scan&parse str)))])
      (apply-subst-to-sexp (canonical-subst ty-sexp) ty-sexp))))

(define str0 "proc (x: ?) x")
(type-eq? str0 '(t37 -> t37))
(type-not-eq? str0 '(t73 -> t37))

(define str1 "proc (x: ?) -(x, 3)")
(type-eq? str1 '(int -> int))

(define str2 "proc (x: ?) proc (y: ?) (x y)")
(type-eq? str2 '((t0 -> t1) -> (t0 -> t1)))

(define str3 "proc (x: ?) (x 3)")
(type-eq? str3 '((int -> t0) -> t0))

(define str4 "proc (x: ?) (x x)")
; (:t str4) ; should fail

(define str5 "proc (x: ?) if x then 88 else 99")
(type-eq? str5 '(bool -> int))

(define str6 "proc (x: ?) proc (y: ?) if x then y else 99")
(type-eq? str6 '(bool -> (int -> int)))

(define str7 "(proc (p: ?) if p then 88 else 99
               33)")
; (:t str7) ; should fail

(define str8
  "proc (f: ?)
    proc (g: ?)
      proc (p: ?)
        proc (x: ?) if (p (f x)) then (g 1) else -((f x),1)")

(type-eq? str8
          '((t1 -> int) -> ((int -> int) -> ((int -> bool) -> (t1 -> int)))))

(define str9
  " proc (x: ?)
                 proc(p: ?)
                   proc (f: ?)
                     if (p x) then -(x,1) else (f p)")
(type-eq? str9 '(int -> ((int -> bool) -> (((int -> bool) -> int) -> int))))

(define str10
  "proc (f: ?)
                 let d = proc (x: ?)
                           proc (z: ?) ((f (x x)) z)
                 in proc (n: ?) ((f (d d)) n)")
; (:t str10) ; should fail

(define str11
  "letrec
     ? double (x : ?) = if zero?(x)
                           then 0
                           else -((double -(x,1)), -2)
   in double")
(type-eq? str11 '(int -> int))

(define str12 "proc (x: ?) if x then x else 99")
; (:t str12) ; should fail
