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
    (expression ("let" (arbno identifier "=" expression) "in" expression)
                let-exp)
    (expression ("proc" "(" (separated-list identifier ":" optional-type ",") ")" expression)
                proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("letrec" (arbno optional-type
                                 identifier
                                 "("
                                 (separated-list identifier ":" optional-type ",")
                                 ")"
                                 "="
                                 expression)
                          "in"
                          expression)
                letrec-exp)
    (optional-type ("?") no-type)
    (optional-type (type) a-type)
    (type ("int") int-type)
    (type ("bool") bool-type)
    (type ("(" (separated-list type "*") "->" type ")") proc-type)
    (type ("%tvar-type" number) tvar-type)))

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse (sllgen:make-string-parser the-lexical-spec the-grammar))

(define proc-type?
  (lambda (ty) (cases type ty [proc-type (t1 t2) #t] [else #f])))

(define tvar-type?
  (lambda (ty) (cases type ty [tvar-type (serial-number) #t] [else #f])))

(define proc-type->args-types
  (lambda (ty)
    (cases
     type
     ty
     [proc-type (args-types result-type) args-types]
     [else (eopl:error 'proc-type->args-types "Not a proc type: ~s" ty)])))

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
    (cases
     type
     ty
     (int-type () 'int)
     (bool-type () 'bool)
     (proc-type (args-types result-type)
                (if (null? args-types)
                    (type-to-external-form result-type)
                    (let loop ([first (car args-types)] [rest (cdr args-types)])
                      (if (null? rest)
                          (list (type-to-external-form first)
                                '->
                                (type-to-external-form result-type))
                          (cons (type-to-external-form first)
                                (cons '* (loop (car rest) (cdr rest))))))))
     (tvar-type (serial-number)
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
           (proc-type (args-types result-type)
                      (proc-type (map (lambda (arg-type)
                                        (apply-one-subst arg-type tvar ty1))
                                      args-types)
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
     (proc-type (args-types result-type)
                (proc-type (map (lambda (arg-type)
                                  (apply-subst-to-type arg-type subst))
                                args-types)
                           (apply-subst-to-type result-type subst)))
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
        [(and (proc-type? ty1) (proc-type? ty2))
         (let unifier-args ([args-types-ty1 (proc-type->args-types ty1)]
                            [args-types-ty2 (proc-type->args-types ty2)]
                            [subst subst])
           (if (null? args-types-ty1)
               (unifier (proc-type->result-type ty1)
                        (proc-type->result-type ty2)
                        subst
                        exp)
               (let ([new-subst (unifier (car args-types-ty1)
                                         (car args-types-ty2)
                                         subst
                                         exp)])
                 (unifier-args (cdr args-types-ty1)
                               (cdr args-types-ty2)
                               new-subst))))]
        [else (report-unification-failure ty1 ty2 exp)]))))

(define every?
  (lambda (pred lst)
    (cond
      [(null? lst) #t]
      [(pred (car lst)) (every? pred (cdr lst))]
      [else #f])))
; no-occurrence? : Tvar × Type → Bool
(define no-occurrence?
  (lambda (tvar ty)
    (cases
     type
     ty
     (int-type () #t)
     (bool-type () #t)
     (proc-type (args-types result-type)
                (and (every? (lambda (arg-type) (no-occurrence? tvar arg-type))
                             args-types)
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

(define extend-tenv*
  (lambda (vars types tenv)
    (if (not (= (length vars) (length types)))
        (eopl:error 'extend-tenv*)
        (let loop ([vars vars] [types types])
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
     (let-exp (vars exps body)
              (let loop ([vars vars] [exps exps] [tenv tenv] [subst subst])
                (if (null? vars)
                    (type-of body tenv subst)
                    (cases answer
                           (type-of (car exps) tenv subst)
                           (an-answer (ty1 subst)
                                      (loop (cdr vars)
                                            (cdr exps)
                                            (extend-tenv (car vars) ty1 tenv)
                                            subst))))))
     (proc-exp (vars otypes body)
               (let ([args-types (map otype->type otypes)])
                 (cases answer
                        (type-of body (extend-tenv* vars args-types tenv) subst)
                        (an-answer (result-type subst)
                                   (an-answer (proc-type args-types result-type)
                                              subst)))))
     (call-exp
      (rator rands)
      (let loop-rands ([rands rands] [rands-types '()] [subst subst])
        (if (null? rands)
            (let ([result-type (fresh-tvar-type)]
                  [rands-types (reverse rands-types)])
              (cases answer
                     (type-of rator tenv subst)
                     (an-answer (rator-type subst)
                                (let ([subst (unifier rator-type
                                                      (proc-type rands-types
                                                                 result-type)
                                                      subst
                                                      exp)])
                                  (an-answer result-type subst)))))
            (cases answer
                   (type-of (car rands) tenv subst)
                   (an-answer (rand-type subst)
                              (loop-rands (cdr rands)
                                          (cons rand-type rands-types)
                                          subst))))))
     (letrec-exp
      (proc-result-otypes proc-names
                          bvarss
                          proc-args-otypess
                          proc-bodies
                          letrec-body)
      (let ([proc-result-types (map otype->type proc-result-otypes)]
            [proc-args-typess (map (lambda (proc-args-otypes)
                                     (map otype->type proc-args-otypes))
                                   proc-args-otypess)])
        (let ([tenv-for-letrec-body
               (extend-tenv*
                proc-names
                (map (lambda (proc-args-types proc-result-type)
                       (proc-type proc-args-types proc-result-type))
                     proc-args-typess
                     proc-result-types)
                tenv)])
          (let loop-procs ([proc-bodies proc-bodies]
                           [bvarss bvarss]
                           [proc-result-types proc-result-types]
                           [proc-args-typess proc-args-typess]
                           [subst subst])
            (if (null? proc-bodies)
                (type-of letrec-body tenv-for-letrec-body subst)
                (cases answer
                       (type-of (car proc-bodies)
                                (extend-tenv* (car bvarss)
                                              (car proc-args-typess)
                                              tenv-for-letrec-body)
                                subst)
                       (an-answer (proc-body-type subst)
                                  (let ([subst (unifier proc-body-type
                                                        (car proc-result-types)
                                                        subst
                                                        (car proc-bodies))])
                                    (loop-procs (cdr proc-bodies)
                                                (cdr bvarss)
                                                (cdr proc-result-types)
                                                (cdr proc-args-typess)
                                                subst))))))))))))

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


(define str12
  "proc(x: ?, y: ?, z: ?)
     if (z 10 11 true)
     then 12
     else if y
          then x
          else -(x, 1)")
(type-eq? str12 '(int * bool * (int * int * bool -> bool) -> int))

(define str13 "proc() 0")
(type-eq? str13 'int)

(define str14
  "let x = 11
       y = 13
       f = proc(a: ?, b: ?)
             zero?(-(a, b))
       g = proc(a: ?, b: ?, c: ?)
             if (c a b) then false else true
   in (g x y f)")
(type-eq? str14 'bool)

(define str15
  " 
   letrec
     int add(a: ?, b: ?) = -(a, -(0, b))
     int mul(a: ?, b: ?) = if zero?(b) then 0 else (add a (mul a -(b, 1)))
     int fib(a: ?, b: ?, n: ?) = if zero?(n) then b else (fib b -(a, -(0, b)) -(n, 1))
     int factk(n: ?, k: ?) = if zero?(n) then (k 1) else (factk -(n, 1) proc(v0: int) (k (mul v0 n)))
   in -((factk 10 proc(x: ?) x), (fib 0 1 10))")
(type-eq? str15 'int)
