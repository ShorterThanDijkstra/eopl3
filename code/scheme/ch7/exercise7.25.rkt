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
    (expression ("list" "(" expression (arbno "," expression) ")") list-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("null?" "(" expression ")") null?-exp)
    (expression ("emptylist") emptylist-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
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
    (type ("listof" type) list-type)
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

(define list-type? (lambda (ty) (cases type ty [list-type (ty) #t] [else #f])))

(define list-type->type
  (lambda (ty)
    (cases type
           ty
           [list-type (ty) ty]
           [else (eopl:error 'list-type->type "Not a list type: ~s" ty)])))

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
           (list-type (ty) (list 'list-type (type-to-external-form ty)))
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
           (list-type (ty) (list-type (apply-one-subst ty tvar ty1)))
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
     (list-type (ty) (list-type (apply-subst-to-type ty subst)))
     (proc-type (t1 t2)
                (proc-type (apply-subst-to-type t1 subst)
                           (apply-subst-to-type t2 subst)))
     (tvar-type (sn) (let ([tmp (assoc ty subst)]) (if tmp (cdr tmp) ty))))))

; empty-subst : () → Subst
(define empty-subst (lambda () '()))

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
        [(and (list-type? ty1) (list-type? ty2))
         (unifier (list-type->type ty1) (list-type->type ty2) subst exp)]
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
           (list-type (ty1) (no-occurrence? tvar ty1))
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
           (a-program (exp1)
                      (cases answer
                             (type-of exp1 (init-tenv) (empty-subst))
                             (an-answer (ty subst)
                                        (apply-subst-to-type ty subst)))))))

;; type-of: Exp * Tenv * Subst  -> Answer
(define type-of
  (lambda (exp tenv subst)
    (cases
     expression
     exp
     (const-exp (num) (an-answer (int-type) subst))
     (zero?-exp
      (exp1)
      (cases answer
             (type-of exp1 tenv subst)
             (an-answer (type1 subst1)
                        (let ([subst2 (unifier type1 (int-type) subst1 exp)])
                          (an-answer (bool-type) subst2)))))
     (diff-exp
      (exp1 exp2)
      (cases answer
             (type-of exp1 tenv subst)
             (an-answer
              (type1 subst1)
              (let ([subst1 (unifier type1 (int-type) subst1 exp1)])
                (cases answer
                       (type-of exp2 tenv subst1)
                       (an-answer
                        (type2 subst2)
                        (let ([subst2 (unifier type2 (int-type) subst2 exp2)])
                          (an-answer (int-type) subst2))))))))
     (if-exp
      (exp1 exp2 exp3)
      (cases answer
             (type-of exp1 tenv subst)
             (an-answer
              (ty1 subst)
              (let ([subst (unifier ty1 (bool-type) subst exp1)])
                (cases answer
                       (type-of exp2 tenv subst)
                       (an-answer
                        (ty2 subst)
                        (cases answer
                               (type-of exp3 tenv subst)
                               (an-answer
                                (ty3 subst)
                                (let ([subst (unifier ty2 ty3 subst exp)])
                                  (an-answer ty2 subst))))))))))
     (var-exp (var) (an-answer (apply-tenv tenv var) subst))
     (list-exp (fst rest)
               (cases answer
                      (type-of fst tenv subst)
                      (an-answer
                       (fst-ty subst)
                       (let loop ([rest rest] [subst subst])
                         (if (null? rest)
                             (an-answer (list-type fst-ty) subst)
                             (cases answer
                                    (type-of (car rest) tenv subst)
                                    (an-answer
                                     (ty subst)
                                     (let ([new-subst
                                            (unifier ty fst-ty subst exp)])
                                       (loop (cdr rest) new-subst)))))))))
     (cons-exp
      (fst rest)
      (cases
       answer
       (type-of fst tenv subst)
       (an-answer
        (fst-ty subst)
        (cases
         answer
         (type-of rest tenv subst)
         (an-answer
          (rest-ty subst)
          (let ([subst (unifier fst-ty (list-type->type rest-ty) subst exp)])
            (an-answer rest-ty subst)))))))
     (null?-exp
      (exp1)
      (cases answer
             (type-of exp1 tenv subst)
             (an-answer
              (exp1-ty subst)
              (let ([tvar1 (fresh-tvar-type)])
                (let ([subst (unifier (list-type tvar1) exp1-ty subst exp1)])
                  (an-answer (bool-type) subst))))))
     (emptylist-exp () (an-answer (list-type (fresh-tvar-type)) subst))
     (car-exp
      (exp1)
      (cases answer
             (type-of exp1 tenv subst)
             (an-answer
              (exp1-ty subst)
              (let ([tvar1 (fresh-tvar-type)])
                (let ([subst (unifier (list-type tvar1) exp1-ty subst exp1)])
                  (an-answer tvar1 subst))))))
     (cdr-exp
      (exp1)
      (cases answer
             (type-of exp1 tenv subst)
             (an-answer
              (exp1-ty subst)
              (let ([tvar1 (fresh-tvar-type)])
                (let ([subst (unifier (list-type tvar1) exp1-ty subst exp1)])
                  (an-answer exp1-ty subst))))))
     (let-exp (var exp1 body)
              (cases answer
                     (type-of exp1 tenv subst)
                     (an-answer
                      (rhs-type subst)
                      (type-of body (extend-tenv var rhs-type tenv) subst))))
     (proc-exp (var otype body)
               (let ([arg-type (otype->type otype)])
                 (cases answer
                        (type-of body (extend-tenv var arg-type tenv) subst)
                        (an-answer (result-type subst)
                                   (an-answer (proc-type arg-type result-type)
                                              subst)))))
     (call-exp (rator rand)
               (let ([result-type (fresh-tvar-type)])
                 (cases answer
                        (type-of rator tenv subst)
                        (an-answer
                         (rator-type subst)
                         (cases answer
                                (type-of rand tenv subst)
                                (an-answer
                                 (rand-type subst)
                                 (let ([subst (unifier rator-type
                                                       (proc-type rand-type
                                                                  result-type)
                                                       subst
                                                       exp)])
                                   (an-answer result-type subst))))))))
     (letrec-exp
      (proc-result-otype proc-name bvar proc-arg-otype proc-body letrec-body)
      (let ([proc-result-type (otype->type proc-result-otype)]
            [proc-arg-type (otype->type proc-arg-otype)])
        (let ([tenv-for-letrec-body
               (extend-tenv proc-name
                            (proc-type proc-arg-type proc-result-type)
                            tenv)])
          (cases
           answer
           (type-of proc-body
                    (extend-tenv bvar proc-arg-type tenv-for-letrec-body)
                    subst)
           (an-answer
            (proc-body-type subst)
            (let ([subst
                   (unifier proc-body-type proc-result-type subst proc-body)])
              (type-of letrec-body tenv-for-letrec-body subst))))))))))

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

(define str12 "list(1, 2, 3)")
  
(type-eq? str12 '(list-type int))
; (:t "list(1, true") ; should fail

(define str13 "cons(zero?(1), list(false, true))")
(type-eq? str13 '(list-type bool))
; (:t "cons(true, list(1, 2, 3))")  ; should fail

(define str14 "cons(1, emptylist)")
(type-eq? str14 '(list-type int))

(define str15 "null?(emptylist)")
(type-eq? str15 'bool)
; (:t "null?(1)") ; should fail

(define str16 "car(list(1, 2))")
(type-eq? str16 'int)

(define str17 "car(emptylist)")
(type-eq? str17 't0)

(define str18 "cdr(list(1, 2))")
(type-eq? str18 '(list-type int))

(define str19 "cdr(emptylist)")
(type-eq? str19 '(list-type t37))

(define str20 "proc(x: ?)
                proc(y: ?)
                  if zero?(x)
                     then list(y)
                     else list(x)")
(type-eq? str20 '(int -> (int -> (list-type int))))