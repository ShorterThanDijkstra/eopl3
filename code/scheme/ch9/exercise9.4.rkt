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

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda ()
    (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

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

;; newref : ExpVal -> Ref
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
  (an-object (c class?)
             (fields-vals (list-of reference?))))
(define object->class
  (lambda (obj)
    (cases object obj
      (an-object (c fields-vals)
                 c))))

(define object->fields
  (lambda (obj)
    (cases object obj
      (an-object (c fields-vals)
                 fields-vals))))

;; new-object : ClassName -> Obj
; (define new-object
;   (lambda (class-name)
;     (an-object class-name
;                (map (lambda (field-name)
;                       (newref (list 'uninitialized-field field-name)))
;                     (class->field-names (lookup-class class-name))))))
(define new-object
  (lambda (class-name)
    (let ([c (lookup-class class-name)])
      (an-object c
                 (map (lambda (field-name)
                        (newref (list 'uninitialized-field field-name)))
                      (class->field-names c))))))


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

(define find-method-in-class
  (lambda (c name)
     (let ([m-env (class->method-env c)])
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
    (map
     (lambda (m-decl)
       (cases method-decl
         m-decl
         (a-method-decl
          (method-name vars body)
          (list method-name
                (a-method vars body super-name field-names)))))
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

; (define object->class-name
;   (lambda (obj)
;     (cases object obj (an-object (class-name fields) class-name))))

; (define object->fields
;   (lambda (obj)
;     (cases object obj (an-object (class-decl fields) fields))))

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
  (procedure (vars (list-of symbol?))
             (body expression?)
             (env environment?)))

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
          (var body saved-env)
          (list 'procedure var '... (env->list saved-env)))))
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
;;; interp
;;;;;;;;;;;;;;;; switches for instrument-let ;;;;;;;;;;;;;;;;

(define instrument-let (make-parameter #f))

;; say (instrument-let #t) to turn instrumentation on.
;;     (instrument-let #f) to turn it off again.

;;;;;;;;;;;;;;;; the interpreter ;;;;;;;;;;;;;;;;

;; value-of-program : Program -> ExpVal
(define value-of-program
  (lambda (pgm)
    (initialize-store!)
    (cases program
      pgm
      (a-program (class-decls body)
                 (initialize-class-env! class-decls)
                 (value-of body (init-env))))))

;; value-of : Exp * Env -> ExpVal
(define value-of
  (lambda (exp env)
    (cases
        expression
      exp
      (const-exp (num) (num-val num))
      (var-exp (var) (deref (apply-env env var)))
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
      (let-exp
       (vars exps body)
       (when (instrument-let)
         (eopl:printf "entering let ~s~%" vars))
       (let ([new-env (extend-env
                       vars
                       (map newref (values-of-exps exps env))
                       env)])
         (when (instrument-let)
           (begin
             (eopl:printf "entering body of let ~s with env =~%" vars)
             (eopl:pretty-print (env->list new-env))
             (eopl:printf "store =~%")
             (eopl:pretty-print (store->readable (get-store-as-list)))
             (eopl:printf "~%")))
         (value-of body new-env)))
      (proc-exp (bvars body) (proc-val (procedure bvars body env)))
      (call-exp (rator rands)
                (let ([proc (expval->proc (value-of rator env))]
                      [args (values-of-exps rands env)])
                  (apply-procedure proc args)))
      (letrec-exp
       (p-names b-varss p-bodies letrec-body)
       (value-of letrec-body
                 (extend-env-rec** p-names b-varss p-bodies env)))
      (begin-exp
        (exp1 exps)
        (letrec ([value-of-begins
                  (lambda (e1 es)
                    (let ([v1 (value-of e1 env)])
                      (if (null? es)
                          v1
                          (value-of-begins (car es) (cdr es)))))])
          (value-of-begins exp1 exps)))
      (assign-exp (x e)
                  (begin
                    (setref! (apply-env env x) (value-of e env))
                    (num-val 27)))
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
      (self-exp () (apply-env env '%self))
      (method-call-exp
       (obj-exp method-name rands)
       (let ([args (values-of-exps rands env)]
             [obj (value-of obj-exp env)])
        
         (apply-method
          (find-method-in-class (object->class obj) method-name)
          obj
          args)))
      (super-call-exp
       (method-name rands)
       (let ([args (values-of-exps rands env)]
             [obj (apply-env env '%self)])
         (apply-method
          (find-method (apply-env env '%super) method-name)
          obj
          args))))))

;; apply-procedure : Proc * Listof(ExpVal) -> ExpVal
(define apply-procedure
  (lambda (proc1 args)
    (cases
        proc
      proc1
      (procedure
       (vars body saved-env)
       (let ([new-env (extend-env vars (map newref args) saved-env)])
         (when (instrument-let)
           (begin
             (eopl:printf "entering body of proc ~s with env =~%" vars)
             (eopl:pretty-print (env->list new-env))
             (eopl:printf "store =~%")
             (eopl:pretty-print (store->readable (get-store-as-list)))
             (eopl:printf "~%")))
         (value-of body new-env))))))

;; apply-method : Method * Obj * Listof(ExpVal) -> ExpVal
(define apply-method
  (lambda (m self args)
    (cases method
      m
      (a-method (vars body super-name field-names)
                (value-of body
                          (extend-env
                           vars
                           (map newref args)
                           (extend-env-with-self-and-super
                            self
                            super-name
                            (extend-env field-names
                                        (object->fields self)
                                        (empty-env)))))))))

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
