#lang eopl

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; lang
(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define the-grammar
  '((program ((arbno class-decl) expression) a-program)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("+" "(" expression "," expression ")") sum-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression)
                if-exp)
    (expression (identifier) var-exp)
    (expression
     ("let" (arbno identifier "=" expression) "in" expression)
     let-exp)
    (expression
     ("proc" "(" (separated-list identifier ",") ")" expression)
     proc-exp)
    (expression ("null?" "(" expression ")") null?-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("letrec" (arbno identifier
                                 "("
                                 (separated-list identifier ",")
                                 ")"
                                 "="
                                 expression)
                          "in"
                          expression)
                letrec-exp)
    (expression ("begin" expression (arbno ";" expression) "end")
                begin-exp)
    (expression ("set" identifier "=" expression) assign-exp)
    (expression ("list" "(" (separated-list expression ",") ")")
                list-exp)
    ;; new productions for oop
    (class-decl ("class" identifier
                         "extends"
                         identifier
                         (arbno "field" identifier)
                         (arbno method-decl))
                a-class-decl)
    (method-decl ("method" identifier
                           "("
                           (separated-list identifier ",")
                           ")" ; method formals
                           expression)
                 a-method-decl)
    (expression
     ("new" identifier "(" (separated-list expression ",") ")")
     new-object-exp)
    ;; this is special-cased to prevent it from mutation
    (expression ("self") self-exp)
    (expression ("send" expression
                        identifier
                        "("
                        (separated-list expression ",")
                        ")")
                method-call-exp)
    (expression
     ("super" identifier "(" (separated-list expression ",") ")")
     super-call-exp)))

; (sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda ()
    (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

(define-datatype program
  program?
  (a-program (a-program48 (list-of class-decl?))
             (a-program49 expression?)))

(define-datatype
  class-decl
  class-decl?
  (a-class-decl (a-class-decl50 symbol?)
                (a-class-decl51 symbol?)
                (a-class-decl52 (list-of symbol?))
                (a-class-decl53 (list-of method-decl?))))

(define-datatype method-decl
  method-decl?
  (a-method-decl (a-method-decl54 symbol?)
                 (a-method-decl55 (list-of symbol?))
                 (a-method-decl56 expression?)))

(define-datatype
  expression
  expression?
  (const-exp (const-exp57 number?))
  (diff-exp (diff-exp58 expression?) (diff-exp59 expression?))
  (sum-exp (sum-exp60 expression?) (sum-exp61 expression?))
  (zero?-exp (zero?-exp62 expression?))
  (if-exp (if-exp63 expression?)
          (if-exp64 expression?)
          (if-exp65 expression?))
  (var-exp (var-exp66 symbol?))
  (let-exp (let-exp67 (list-of symbol?))
           (let-exp68 (list-of expression?))
           (let-exp69 expression?))
  (proc-exp (proc-exp70 (list-of symbol?)) (proc-exp71 expression?))
  (null?-exp (null?-exp72 expression?))
  (car-exp (car-exp73 expression?))
  (cdr-exp (cdr-exp74 expression?))
  (cons-exp (cons-exp75 expression?) (cons-exp76 expression?))
  (call-exp (call-exp77 expression?)
            (call-exp78 (list-of expression?)))
  (letrec-exp (letrec-exp79 (list-of symbol?))
              (letrec-exp80 (list-of (list-of symbol?)))
              (letrec-exp81 (list-of expression?))
              (letrec-exp82 expression?))
  (begin-exp (begin-exp83 expression?)
             (begin-exp84 (list-of expression?)))
  (assign-exp (assign-exp85 symbol?) (assign-exp86 expression?))
  (list-exp (list-exp87 (list-of expression?)))
  (new-object-exp (new-object-exp88 symbol?)
                  (new-object-exp89 (list-of expression?)))
  (self-exp)
  (nameless-self-exp (self-n number?))
  (method-call-exp (method-call-exp90 expression?)
                   (method-call-exp91 symbol?)
                   (method-call-exp92 (list-of expression?)))
  (super-call-exp (super-call-exp93 symbol?)
                  (super-call-exp94 (list-of expression?)))
  (nameless-super-call-exp (super-call-exp93 symbol?)
                           (super-call-exp94 (list-of expression?))
                           (self-n number?)
                           (super-n number?)
                           )
  (nameless-var-exp (nameless-var-exp95 number?))
  (nameless-assign-exp (nameless-assign-exp96 number?)
                       (nameless-assign-exp97 expression?))
  (nameless-let-exp (nameless-let-exp98 (list-of expression?))
                    (nameless-let-exp99 expression?))
  (nameless-letrec-exp (nameless-letrec-exp100 (list-of expression?))
                       (nameless-letrec-exp101 expression?))
  (nameless-proc-exp (nameless-proc-exp102 expression?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; store
(define instrument-newref (make-parameter #f))

;;;;;;;;;;;;;;;; references and the store ;;;;;;;;;;;;;;;;

;;; world's dumbest model of the store:  the store is a list and a
;;; reference is number which denotes a position in the list.

;; the-store: a Scheme variable containing the current state of the
;; store.  Initially set to a dummy variable.
(define the-store 'uninitialized)

;; empty-store : () -> Sto
(define empty-store (lambda () '()))

;; initialize-store! : () -> Sto
;; usage: (initialize-store!) sets the-store to the empty-store
(define initialize-store! (lambda () (set! the-store (empty-store))))

;; get-store : () -> Sto
;; This is obsolete.  Replaced by get-store-as-list below
(define get-store (lambda () the-store))

;; reference? : SchemeVal -> Bool
(define reference? (lambda (v) (integer? v)))

;; newref : Either(ExpVal, Object, Symbol) -> Ref
(define newref
  (lambda (val)
    (let ([next-ref (length the-store)])
      (set! the-store (append the-store (list val)))
      (when (instrument-newref)
        (eopl:printf
         "newref: allocating location ~s with initial contents ~s~%"
         next-ref
         val))
      next-ref)))

;; deref : Ref -> ExpVal
(define deref (lambda (ref) (list-ref the-store ref)))

;; setref! : Ref * ExpVal -> Unspecified
(define setref!
  (lambda (ref val)
    (set!
     the-store
     (letrec (;; returns a list like store1, except that position ref1
              ;; contains val.
              [setref-inner
               (lambda (store1 ref1)
                 (cond
                   [(null? store1)
                    (report-invalid-reference ref the-store)]
                   [(zero? ref1) (cons val (cdr store1))]
                   [else
                    (cons (car store1)
                          (setref-inner (cdr store1) (- ref1 1)))]))])
       (setref-inner the-store ref)))))

(define report-invalid-reference
  (lambda (ref the-store)
    (eopl:error 'setref
                "illegal reference ~s in store ~s"
                ref
                the-store)))

;; get-store-as-list : () -> Listof(List(Ref,Expval))
;; Exports the current state of the store as a scheme list.
;; (get-store-as-list '(foo bar baz)) = ((0 foo)(1 bar) (2 baz))
;;   where foo, bar, and baz are expvals.
;; If the store were represented in a different way, this would be
;; replaced by something cleverer.
;; Replaces get-store
(define get-store-as-list
  (lambda ()
    (letrec (;; convert sto to list as if its car was location n
             [inner-loop
              (lambda (sto n)
                (if (null? sto)
                    '()
                    (cons (list n (car sto))
                          (inner-loop (cdr sto) (+ n 1)))))])
      (inner-loop the-store 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; classes
;;;;;;;;;;;;;;;; objects ;;;;;;;;;;;;;;;;

;; an object consists of a symbol denoting its class, and a list of
;; references representing the managed storage for the all the fields.

(define identifier? symbol?)

(define-datatype object
  object?
  (an-object (class-name identifier?)
             (fields (list-of reference?))))

;; new-object : ClassName -> Obj
(define new-object
  (lambda (class-name)
    (an-object class-name
               (map (lambda (field-name)
                      (newref (list 'uninitialized-field field-name)))
                    (class->field-names (lookup-class class-name))))))

;;;;;;;;;;;;;;;; methods and method environments ;;;;;;;;;;;;;;;;

(define-datatype method
  method?
  (a-method (vars (list-of symbol?))
            (body expression?)
            (super-name symbol?)
            (field-names (list-of symbol?))))

;;;;;;;;;;;;;;;; method environments ;;;;;;;;;;;;;;;;

;; a method environment looks like ((method-name method) ...)

(define method-environment?
  (list-of (lambda (p)
             (and (pair? p) (symbol? (car p)) (method? (cadr p))))))

;; method-env * id -> (maybe method)
(define assq-method-env
  (lambda (m-env id)
    (cond
      [(assq id m-env)
       =>
       cadr]
      [else #f])))

;; find-method : Sym * Sym -> Method
(define find-method
  (lambda (c-name name)
    (let ([m-env (class->method-env (lookup-class c-name))])
      (let ([maybe-pair (assq name m-env)])
        (if (pair? maybe-pair)
            (cadr maybe-pair)
            (report-method-not-found name))))))

(define report-method-not-found
  (lambda (name) (eopl:error 'find-method "unknown method ~s" name)))

;; merge-method-envs : MethodEnv * MethodEnv -> MethodEnv
(define merge-method-envs
  (lambda (super-m-env new-m-env) (append new-m-env super-m-env)))

;; method-decls->method-env :
;; Listof(MethodDecl) * ClassName * Listof(FieldName) -> MethodEnv
(define method-decls->method-env
  (lambda (m-decls super-name field-names)
    (map (lambda (m-decl)
           (cases method-decl
             m-decl
             (a-method-decl
              (method-name vars body)
              (let ([m-senv (extend-senv*
                             vars
                             (extend-senv
                              '%self
                              (extend-senv '%super
                                           (extend-senv*
                                            field-names
                                            (empty-senv)))))])
                (list method-name
                      (a-method vars
                                (translation-of
                                 body
                                 m-senv )
                                super-name
                                field-names))))))
         m-decls)))
;;;;;;;;;;;;;;;; classes ;;;;;;;;;;;;;;;;

(define-datatype class
  class?
  (a-class (super-name (maybe symbol?))
           (field-names (list-of symbol?))
           (method-env method-environment?)))

;;;;;;;;;;;;;;;; class environments ;;;;;;;;;;;;;;;;

;; the-class-env will look like ((class-name class) ...)

;; the-class-env : ClassEnv
(define the-class-env '())

;; add-to-class-env! : ClassName * Class -> Unspecified
(define add-to-class-env!
  (lambda (class-name class)
    (set! the-class-env
          (cons (list class-name class) the-class-env))))

;; lookup-class : ClassName -> Class
(define lookup-class
  (lambda (name)
    (let ([maybe-pair (assq name the-class-env)])
      (if maybe-pair (cadr maybe-pair) (report-unknown-class name)))))

(define report-unknown-class
  (lambda (name) (eopl:error 'lookup-class "Unknown class ~s" name)))

;; constructing classes

;; initialize-class-env! : Listof(ClassDecl) -> Unspecified
(define initialize-class-env!
  (lambda (c-decls)
    (set! the-class-env (list (list 'object (a-class #f '() '()))))
    (for-each initialize-class-decl! c-decls)))

;; initialize-class-decl! : ClassDecl -> Unspecified
(define initialize-class-decl!
  (lambda (c-decl)
    (cases class-decl
      c-decl
      (a-class-decl
       (c-name s-name f-names m-decls)
       (let ([f-names (append-field-names
                       (class->field-names (lookup-class s-name))
                       f-names)])
         (add-to-class-env!
          c-name
          (a-class s-name
                   f-names
                   (merge-method-envs
                    (class->method-env (lookup-class s-name))
                    (method-decls->method-env m-decls
                                              s-name
                                              f-names)))))))))

;; exercise:  rewrite this so there's only one set! to the-class-env.

;; append-field-names :  Listof(FieldName) * Listof(FieldName)
;;                       -> Listof(FieldName)
;; like append, except that any super-field that is shadowed by a
;; new-field is replaced by a gensym
(define append-field-names
  (lambda (super-fields new-fields)
    (cond
      [(null? super-fields) new-fields]
      [else
       (cons (if (memq (car super-fields) new-fields)
                 (fresh-identifier (car super-fields))
                 (car super-fields))
             (append-field-names (cdr super-fields) new-fields))])))

;;;;;;;;;;;;;;;; selectors ;;;;;;;;;;;;;;;;

(define class->super-name
  (lambda (c-struct)
    (cases class
      c-struct
      (a-class (super-name field-names method-env) super-name))))

(define class->field-names
  (lambda (c-struct)
    (cases class
      c-struct
      (a-class (super-name field-names method-env)
               field-names))))

(define class->method-env
  (lambda (c-struct)
    (cases class
      c-struct
      (a-class (super-name field-names method-env) method-env))))

(define object->class-name
  (lambda (obj)
    (cases object obj (an-object (class-name fields) class-name))))

(define object->fields
  (lambda (obj)
    (cases object obj (an-object (class-decl fields) fields))))

(define fresh-identifier
  (let ([sn 0])
    (lambda (identifier)
      (set! sn (+ sn 1))
      (string->symbol
       (string-append (symbol->string identifier)
                      "%" ; this can't appear in an input identifier
                      (number->string sn))))))

(define maybe (lambda (pred) (lambda (v) (or (not v) (pred v)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; data structures

;;;;;;;;;;;;;;;; expressed values ;;;;;;;;;;;;;;;;
;;; an expressed value is either a number, a boolean, a procval, or a
;;; reference.

(define-datatype expval
  expval?
  (num-val (value number?))
  (bool-val (boolean boolean?))
  (proc-val (proc proc?))
  ;  (ref-val (ref reference?)) ;why this
  (obj-val (obj object?))
  (list-val (lst (list-of expval?))))

;;; extractors:

(define expval->num
  (lambda (v)
    (cases expval
      v
      (num-val (num) num)
      (else (expval-extractor-error 'num v)))))

(define expval->bool
  (lambda (v)
    (cases expval
      v
      (bool-val (bool) bool)
      (else (expval-extractor-error 'bool v)))))

(define expval->proc
  (lambda (v)
    (cases expval
      v
      (proc-val (proc) proc)
      (else (expval-extractor-error 'proc v)))))

;; not used.  Nor is expval->obj or expval->list, so we haven't
;; written them.
; (define expval->ref
;   (lambda (v)
;     (cases expval
;            v
;            (ref-val (ref) ref)
;            (else (expval-extractor-error 'reference v)))))

(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors
                "Looking for a ~s, found ~s"
                variant
                value)))

;;;;;;;;;;;;;;;; procedures ;;;;;;;;;;;;;;;;

(define-datatype proc
  proc?
  (procedure  (body expression?)
              (env nameless-environment?)))

(define-datatype
  environment
  environment?
  (empty-env)
  (extend-env (bvars (list-of symbol?))
              (bvals (list-of reference?))
              (saved-env environment?))
  (extend-env-rec** (proc-names (list-of symbol?))
                    (b-varss (list-of (list-of symbol?)))
                    (proc-bodies (list-of expression?))
                    (saved-env environment?))
  (extend-env-with-self-and-super (self object?)
                                  (super-name symbol?)
                                  (saved-env environment?)))

(define nameless-environment?
  (list-of  (lambda (v)
              (or (reference? v)
                  (symbol? v)
                  (object? v)))))

(define empty-nameless-env
  (lambda ()
    '()))


(define extend-nameless-env
  (lambda (val nameless-env)
    (cons val nameless-env)))

(define extend-nameless-env*
  (lambda (vals nameless-env)
    (if (null? vals)
        nameless-env
        (extend-nameless-env (car vals)
                             (extend-nameless-env* (cdr vals)
                                                   nameless-env)))))
(define extend-nameless-rec-env*
  (lambda (exps env)
    (let ([refs (map (lambda (ignore) (newref 'unintialize)) exps)])
      (let ([proc-env (extend-nameless-env* refs env)])
        (let loop ([refs refs]
                   [exps exps])
          (if (null? refs)
              proc-env
              (begin (setref! (car refs) (proc-val (procedure (car exps) proc-env)))
                     (loop (cdr refs) (cdr exps)))))))))

(define list-set
  (lambda (lst n val)
    (cond
      [(null? lst) (eopl:error 'list-set "ran off end")]
      [(zero? n) (cons val (cdr lst))]
      [else (cons (car lst) (list-set (cdr lst) (- n 1) val))])))

(define apply-nameless-env
  (lambda (nameless-env n)
    (list-ref nameless-env n)))

;; env->list : Env -> List
;; used for pretty-printing and debugging
(define env->list
  (lambda (env)
    (cases environment
      env
      (empty-env () '())
      (extend-env (sym val saved-env)
                  (cons (list sym val) (env->list saved-env)))
      (extend-env-rec** (p-names b-varss p-bodies saved-env)
                        (cons (list 'letrec p-names '...)
                              (env->list saved-env)))
      (extend-env-with-self-and-super
       (self super-name saved-env)
       (cons (list 'self self 'super super-name)
             (env->list saved-env))))))

;; expval->printable : ExpVal -> List
;; returns a value like its argument, except procedures get cleaned
;; up with env->list
(define expval->printable
  (lambda (val)
    (cases
        expval
      val
      (proc-val
       (p)
       (cases proc
         p
         (procedure
          ( body saved-env)
          (list 'procedure  '... (env->list saved-env)))))
      (else val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; environment
;;;;;;;;;;;;;;;; initial environment ;;;;;;;;;;;;;;;;

;; init-env : () -> environment

;; (init-env) builds an environment in which i is bound to the
;; expressed value 1, v is bound to the expressed value 5, and x is
;; bound to the expressed value 10.

(define init-env
  (lambda ()
    (extend-env1
     'true
     (newref (bool-val #t))
     (extend-env1 'false (newref (bool-val #f)) (empty-env)))))

(define extend-env1
  (lambda (id val env) (extend-env (list id) (list val) env)))

;;;;;;;;;;;;;;;; environment constructors and observers ;;;;;;;;;;;;;;;;

(define apply-env
  (lambda (env search-sym)
    (cases environment
      env
      (empty-env
       ()
       (eopl:error 'apply-env "No binding for ~s" search-sym))
      (extend-env (bvars bvals saved-env)
                  (cond
                    [(location search-sym bvars)
                     =>
                     (lambda (n) (list-ref bvals n))]
                    [else (apply-env saved-env search-sym)]))
      (extend-env-rec**
       (p-names b-varss p-bodies saved-env)
       (cond
         [(location search-sym p-names)
          =>
          (lambda (n)
            (newref (proc-val (procedure (list-ref b-varss n)
                                         (list-ref p-bodies n)
                                         env))))]
         [else (apply-env saved-env search-sym)]))
      (extend-env-with-self-and-super
       (self super-name saved-env)
       (case search-sym
         [(%self) self]
         [(%super) super-name]
         [else (apply-env saved-env search-sym)])))))

;; location : Sym * Listof(Sym) -> Maybe(Int)
;; (location sym syms) returns the location of sym in syms or #f is
;; sym is not in syms.  We can specify this as follows:
;; if (memv sym syms)
;;   then (list-ref syms (location sym syms)) = sym
;;   else (location sym syms) = #f
(define location
  (lambda (sym syms)
    (cond
      [(null? syms) #f]
      [(eqv? sym (car syms)) 0]
      [(location sym (cdr syms))
       =>
       (lambda (n) (+ n 1))]
      [else #f])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;  lexical addressing

(define empty-senv (lambda () '()))

(define extend-senv (lambda (var senv) (cons var senv)))

(define extend-senv*
  (lambda (vars senv)
    (if (null? vars)
        senv
        (extend-senv (car vars) (extend-senv* (cdr vars) senv)))))

(define apply-senv
  (lambda (senv var)
    ; (eopl:pretty-print senv)
    ; (newline)
    (cond
      [(null? senv) (eopl:error 'report-unbound-var "~s" var)]
      [(eqv? var (car senv)) 0]
      [else (+ 1 (apply-senv (cdr senv) var))])))

(define init-senv
  (lambda () (extend-senv 'true (extend-senv 'false (empty-senv)))))

(define translation-of
  (lambda (exp senv)
    (cases
        expression
      exp
      (const-exp (num) (const-exp num))

      (diff-exp (exp1 exp2)
                (diff-exp (translation-of exp1 senv)
                          (translation-of exp2 senv)))
      (sum-exp (exp1 exp2)
               (sum-exp (translation-of exp1 senv)
                        (translation-of exp2 senv)))
      (zero?-exp (exp1) (zero?-exp (translation-of exp1 senv)))
      (if-exp (exp1 exp2 exp3)
              (if-exp (translation-of exp1 senv)
                      (translation-of exp2 senv)
                      (translation-of exp3 senv)))

      (call-exp (rator rands)
                (call-exp (translation-of rator senv)
                          (map (lambda (rand)
                                 (translation-of rand senv))
                               rands)))
      (begin-exp (exp1 exps)
                 (begin-exp (translation-of exp1 senv)
                            (map (lambda (exp2)
                                   (translation-of exp2 senv))
                                 exps)))
      (list-exp (exps)
                (list-exp (map (lambda (exp1)
                                 (translation-of exp1 senv))
                               exps)))
      (null?-exp (exp1) (null?-exp (translation-of exp1 senv)))
      (car-exp (exp1) (car-exp (translation-of exp1 senv)))
      (cdr-exp (exp1) (cdr-exp (translation-of exp1 senv)))
      (cons-exp (arg1 arg2)
                (cons-exp (translation-of arg1 senv)
                          (translation-of arg2 senv)))
      ;; new cases for CLASSES language
      (new-object-exp
       (class-name rands)
       (new-object-exp
        class-name
        (map (lambda (rand) (translation-of rand senv)) rands)))
      (self-exp () (nameless-self-exp (apply-senv senv '%self)))
      (method-call-exp
       (obj-exp method-name rands)
       (method-call-exp
        (translation-of obj-exp senv)
        method-name
        (map (lambda (rand) (translation-of rand senv)) rands)))
      (super-call-exp
       (method-name rands)
       (nameless-super-call-exp
        method-name
        (map (lambda (rand) (translation-of rand senv)) rands)
        (apply-senv senv '%self)
        (apply-senv senv '%super)
        ))
      (var-exp (var) (nameless-var-exp (apply-senv senv var)))
      (let-exp (vars exps body)
               (nameless-let-exp
                (map (lambda (exp1) (translation-of exp1 senv)) exps)
                (translation-of body (extend-senv* vars senv))))
      (proc-exp (bvars body)
                (nameless-proc-exp
                 (translation-of body (extend-senv* bvars senv))))
      (letrec-exp (p-names b-varss p-bodies letrec-body)
                  (let ([senv-for-body (extend-senv* p-names senv)])
                    (nameless-letrec-exp
                     (map (lambda (p-body b-vars)
                            (translation-of
                             p-body
                             (extend-senv* b-vars senv-for-body)))
                          p-bodies
                          b-varss)
                     (translation-of letrec-body senv-for-body))))
      (assign-exp (var exp1)
                  (nameless-assign-exp  (apply-senv senv var) (translation-of exp1 senv)))
      (nameless-self-exp (n) (eopl:error 'translation-of))
      (nameless-super-call-exp (method-name rands self-n super-n) (eopl:error 'translation-of))
      (nameless-var-exp (n) (eopl:error 'translation-of))
      (nameless-assign-exp (n exp1) (eopl:error 'translation-of))
      (nameless-let-exp (exps body) (eopl:error 'translation-of))
      (nameless-letrec-exp (exps body) (eopl:error 'translation-of))
      (nameless-proc-exp (body) (eopl:error 'translation-of)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; interp
;;;;;;;;;;;;;;;; switches for instrument-let ;;;;;;;;;;;;;;;;

(define instrument-let (make-parameter #f))

;; say (instrument-let #t) to turn instrumentation on.
;;     (instrument-let #f) to turn it off again.

;;;;;;;;;;;;;;;; the interpreter ;;;;;;;;;;;;;;;;
; (define translation-of-program
; (lambda (pgm)
;   (initialize-store!)
;   (cases program
;     pgm
;     (a-program (class-decls body)
;                (initialize-class-env! class-decls)
;                (translation-of body (init-senv))))))

(define init-nameless-env
  (lambda ()
    (let ([env (extend-nameless-env
                (newref (bool-val #f))
                (empty-nameless-env))])
      (extend-nameless-env
       (newref (bool-val #t)) env))))

;; value-of-program : Program -> ExpVal
(define value-of-program
  (lambda (pgm)
    (initialize-store!)
    (cases program
      pgm
      (a-program (class-decls body)
                 (initialize-class-env! class-decls)
                 (value-of (translation-of body (init-senv))
                           (init-nameless-env))))))

; value-of : Exp * Env -> ExpVal
(define value-of
  (lambda (exp env)
    (cases
        expression
      exp
      (const-exp (num) (num-val num))
      (diff-exp (exp1 exp2)
                (let ([val1 (expval->num (value-of exp1 env))]
                      [val2 (expval->num (value-of exp2 env))])
                  (num-val (- val1 val2))))
      (sum-exp (exp1 exp2)
               (let ([val1 (expval->num (value-of exp1 env))]
                     [val2 (expval->num (value-of exp2 env))])
                 (num-val (+ val1 val2))))
      (zero?-exp (exp1)
                 (let ([val1 (expval->num (value-of exp1 env))])
                   (if (zero? val1) (bool-val #t) (bool-val #f))))
      (if-exp (exp0 exp1 exp2)
              (if (expval->bool (value-of exp0 env))
                  (value-of exp1 env)
                  (value-of exp2 env)))

      (call-exp (rator rands)
                (let ([proc (expval->proc (value-of rator env))]
                      [args (values-of-exps rands env)])
                  (apply-procedure proc args)))

      (begin-exp
        (exp1 exps)
        (letrec ([value-of-begins
                  (lambda (e1 es)
                    (let ([v1 (value-of e1 env)])
                      (if (null? es)
                          v1
                          (value-of-begins (car es) (cdr es)))))])
          (value-of-begins exp1 exps)))

      (list-exp (exps) (list-val (values-of-exps exps env)))
      (null?-exp (exp)
                 (let ([val (value-of exp env)])
                   (cases expval
                     val
                     (list-val (vals)
                               (if (null? vals)
                                   (bool-val #t)
                                   (bool-val #f)))
                     (else (eopl:error 'value-of exp)))))
      (car-exp (exp)
               (let ([val (value-of exp env)])
                 (cases expval
                   val
                   (list-val (vals)
                             (if (null? vals)
                                 (eopl:error 'value-of exp)
                                 (car vals)))
                   (else (eopl:error 'value-of exp)))))
      (cdr-exp (exp)
               (let ([val (value-of exp env)])
                 (cases expval
                   val
                   (list-val (vals)
                             (if (null? vals)
                                 (eopl:error 'value-of exp)
                                 (list-val (cdr vals))))
                   (else (eopl:error 'value-of exp)))))
      (cons-exp
       (arg1 arg2)
       (let ([val1 (value-of arg1 env)] [val2 (value-of arg2 env)])
         (cases expval
           val2
           (list-val (vals) (list-val (cons val1 vals)))
           (else (eopl:error 'value-of exp)))))
      ;; new cases for CLASSES language
      (new-object-exp
       (class-name rands)
       (let ([args (values-of-exps rands env)]
             [obj (new-object class-name)])
         (apply-method (find-method class-name 'initialize) obj args)
         obj))
      ;-------------------------------------------------------------------
      (nameless-self-exp (n) (apply-nameless-env env n))
      (method-call-exp
       (obj-exp method-name rands)
       (let ([args (values-of-exps rands env)]
             [obj (value-of obj-exp env)])
         (apply-method
          (find-method (object->class-name obj) method-name)
          obj
          args)))
      (nameless-super-call-exp
       (method-name rands self-n super-n)
       (let ([args (values-of-exps rands env)]
             [obj  (apply-nameless-env env self-n)])
         (apply-method
          (find-method  (apply-nameless-env env super-n) method-name)
          obj
          args)))
      ;-------------------------------------------------------------------
      (nameless-var-exp (n)  (deref (apply-nameless-env env n)))
      (nameless-assign-exp (var e)
                           (begin
                             (setref! (apply-nameless-env env var) (value-of e env))
                             (num-val 27)))
      (nameless-let-exp (exps body)
                        (let ([vals (map (lambda (exp1) (value-of exp1 env)) exps)])
                          (value-of body
                                    (extend-nameless-env* (map newref vals) env))))
      (nameless-letrec-exp (exps body)
                           (let ([new-env
                                  (extend-nameless-rec-env* exps env)])
                             (value-of body new-env)))
      (nameless-proc-exp (body)
                         (proc-val
                          (procedure body env)))
      (super-call-exp (method-name rands) (eopl:error 'value-of))
      (self-exp () (eopl:error 'value-of))
      (var-exp (var) (eopl:error 'value-of))
      (assign-exp (x e) (eopl:error 'value-of))
      (let-exp (vars exps body) (eopl:error 'value-of))
      (proc-exp (bvars body) (eopl:error 'value-of))
      (letrec-exp (p-names b-varss p-bodies letrec-body) (eopl:error 'value-of))
      )))

;; apply-procedure : Proc * Listof(ExpVal) -> ExpVal
(define apply-procedure
  (lambda (proc1 vals)
    (cases proc proc1

      (procedure (body saved-nameless-env)
                 (let ([new-env (extend-nameless-env* (map newref vals) saved-nameless-env)])
                   ;  (eopl:pretty-print new-env)
                   ;  (eopl:pretty-print the-store)
                   ;  (eopl:pretty-print body)
                   ;  (display "------------------------\n")
                   (value-of body new-env))))))


;; apply-method : Method * Obj * Listof(ExpVal) -> ExpVal
(define apply-method
  (lambda (m self args)
    (cases method
      m
      (a-method
       (vars body super-name field-names)
       ;  (eopl:pretty-print field-names)
       ;  (eopl:pretty-print (map deref (object->fields self)))
       ;  (display "-----------------------------\n")
       (value-of body
                 (extend-nameless-env*
                  (map newref args)
                  (extend-nameless-env
                   self
                   (extend-nameless-env
                    super-name
                    (extend-nameless-env*
                     (object->fields self)
                     (empty-nameless-env))))))))))

(define values-of-exps
  (lambda (exps env) (map (lambda (exp) (value-of exp env)) exps)))

;; store->readable : Listof(List(Ref,Expval))
;;                    -> Listof(List(Ref,Something-Readable))
(define store->readable
  (lambda (l)
    (map (lambda (p) (cons (car p) (expval->printable (cadr p)))) l)))

(define :e (lambda (str) (value-of-program (scan&parse str))))

(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; test
(require rackunit)

(define str0
  "
  class c1 extends object
     field y
     method gety() y
  33
  ")
(check-equal? (:e str0) (num-val 33))

(define str1
  "
  class c1 extends object
    method initialize() 0
  let o1 = new c1() in
  11
  ")
(check-equal? (:e str1) (num-val 11))

(define str2
  "
  class c1 extends object
    field s
    method initialize() set s = 44
    method gets() s
    method sets(v) set s = v

  let o1 = new c1()
  in send o1 gets()
  ")
(check-equal? (:e str2) (num-val 44))

(define str3
  "
  class c1 extends object
    field s
    method initialize()set s = 44
    method gets()s
    method sets(v)set s = v

  let o1 = new c1()
      t1 = 0
      t2 = 0
  in begin
       set t1 = send o1 gets();
       send o1 sets(33);
       set t2 = send o1 gets();
       list(t1, t2)
  end
  ")
(check-equal? (:e str3) (list-val (list (num-val 44) (num-val 33))))

(define str4
  "
  class counter extends object
    field count
    method initialize()set count = 0
    method countup()set count = -(count, -1)
    method getcount()count

  let o1 = new counter ()
      t1 = 0
      t2 = 0
  in begin
      set t1 = send o1 getcount();
      send o1 countup();
      set t2 = send o1 getcount();
      list(t1,t2)
  end
  ")
(check-equal? (:e str4) (list-val (list (num-val 0) (num-val 1))))

(define str5
  "
  class counter extends object
    field count
    method initialize() set count = 0
    method countup() set count = -(count, -1)
    method getcount() count

  class c1 extends object
     field n
     field counter1
     method initialize(a_counter)
       begin
         set n = 0;
         set counter1 = a_counter
       end
     method countup()
       begin
        send counter1 countup();
        set n = -(n,-1)
       end
     method getstate() list(n, send counter1 getcount())

  let counter1 = new counter()
  in let o1 = new c1(counter1)
         o2 = new c1(counter1)
  in begin
       send o1 countup();
       send o2 countup();
       send o2 countup();
       list(send o1 getstate(),
            send o2 getstate())
     end
  ")
(check-equal?
 (:e str5)
 (list-val (list (list-val (list (num-val 1) (num-val 3)))
                 (list-val (list (num-val 2) (num-val 3))))))

(define str6
  "
  class c1 extends object
    field x
    field y
    method initialize ()
      begin
        set x = 11;
        set y = 12
      end
    method m1 () -(x,y)
    method m2 () send self m3()
  class c2 extends c1
    field y
    method initialize ()
      begin
        super initialize();
        set y = 22
      end
    method m1 (u,v) -(-(x,u), -(y,v))
    method m3 () 23
  class c3 extends c2
    field x
    field z
    method initialize ()
      begin
        super initialize();
        set x = 31;
        set z = 32
      end
    method m3 () -(x,-(y,z))
  let o3 = new c3()
  in send o3 m1(7,8)
  ")
(check-equal? (:e str6) (num-val -10))

(define str7
  "
  class a extends object
    field i
    field j
    method initialize() 1
    method setup()
      begin
        set i = 15;
        set j = 20;
        50
      end
    method f() send self g()
    method g() -(i,-(0,j))
  class b extends a
    field j
    field k
    method setup()
      begin
        set j = 100;
        set k = 200;
        super setup();
        send self h()
      end
    method g()
      list(i,j,k)
    method h() super g()
  class c extends b
    method g() super h()
    method h() -(k,-(0,j))
  let p = proc(o)
           let u = send o setup ()
           in list(u,
                   send o g(),
                   send o f())
  in list((p new a()),
          (p new b()),
          (p new c()))
")
(check-equal?
 (:e str7)
 (list-val
  (list
   (list-val (list (num-val 50) (num-val 35) (num-val 35)))
   (list-val
    (list (num-val 35)
          (list-val (list (num-val 15) (num-val 100) (num-val 200)))
          (list-val (list (num-val 15) (num-val 100) (num-val 200)))))
   (list-val (list (num-val 300) (num-val 35) (num-val 35))))))

(define str8
  "class c1 extends object
     method initialize () 1
     method m1 () send self m2()
     method m2 () 13
   class c2 extends c1
     method m1 () 22
     method m2 () 23
     method m3 () super m1()
   class c3 extends c2
     method m1 () 32
     method m2 () 33

  let o3 = new c3()
   in send o3 m3()")
(check-equal? (:e str8) (num-val 33))

(define str9
  "class c1 extends object
     field x
     method initialize() set x = 3
   class c2 extends c1
     field y
     method initialize()
       begin
         super initialize();
         set y = 5
       end
     method get_x() x
     method get_y() y

   let o2 = new c2()
   in list(send o2 get_x(), send o2 get_y())")
(check-equal? (:e str9) (list-val (list (num-val 3) (num-val 5))))

(define str10
  "class c1 extends object
     field x
     method initialize() set x = 37
     method m1() x
     method m2() send self m1()
   class c2 extends c1
     field y
     method initialize() begin super initialize();
                               set y = 3
                         end

   let o2 = new c2()
   in send o2 m2()")
(check-equal? (:e str10) (num-val 37))
#|
when apply-method m2, field-names is '(x), (object->fields self) is '(37 3)
|#

(define str11
  "class c1 extends object
     method initialize() 0
     method m1() 11
     method m1(v) +(v, 1)
   let o1 = new c1()
   in send o1 m1(2)")
(check-equal? (:e str11) (num-val 11))

(define str12
  "
  letrec even(x) = if zero?(x) then true else (odd -(x, 1))
         odd(x) = if zero?(x) then false else (even -(x, 1))
  in list((even 6), (odd 8))
   ")
(check-equal? (:e str12) (list-val (list (bool-val #t) (bool-val #f))))

(define str13
  "class c1 extends object
     field x
     method initialize() set x = 7
     method m1() x
     method m2() send self m1()
  class c2 extends c1
     field y
     method initialize() set y = 71
     method m1() y
  let o2 = new c2()
      o1 = new c1()
  in list(send o2 m2(), send o1 m2())")
(check-equal? (:e str13) (list-val (list (num-val 71) (num-val 7))))

(define str14
  "class c1 extends object
     field x
     method initialize() set x = 7
     method getx() x
  class c2 extends c1
     field y
     method initialize() begin super initialize();
                               set y = 71
                         end
     method gety() y
  let o2 = new c2()
  in list(send o2 getx(), send o2 gety())")
(check-equal? (:e str14) (list-val (list (num-val 7) (num-val 71))))