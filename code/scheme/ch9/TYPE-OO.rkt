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
    (expression ("proc" "("
                        (separated-list identifier ":" type ",")
                        ")"
                        expression)
                proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression
     ("letrec" (arbno type
                      identifier
                      "("
                      (separated-list identifier ":" type ",")
                      ")"
                      "="
                      expression)
               "in"
               expression)
     letrec-exp)
    (expression ("begin" expression (arbno ";" expression) "end")
                begin-exp)
    (expression ("set" identifier "=" expression) assign-exp)
    ;; non-empty lists for typechecked version
    (expression ("list" "(" expression (arbno "," expression) ")")
                list-exp)
    ;; new productions for oop
    (class-decl ("class" identifier
                         "extends"
                         identifier
                         (arbno "implements" identifier)
                         (arbno "field" type identifier)
                         (arbno method-decl))
                a-class-decl)
    (method-decl ("method" type
                           identifier
                           "("
                           (separated-list identifier ":" type ",")
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
     super-call-exp)
    ;; new productions for typed-oo
    (class-decl ("interface" identifier (arbno abstract-method-decl))
                an-interface-decl)
    (abstract-method-decl
     ("method" type
               identifier
               "("
               (separated-list identifier ":" type ",")
               ")")
     an-abstract-method-decl)
    (expression ("cast" expression identifier) cast-exp)
    (expression ("instanceof" expression identifier) instanceof-exp)
    (type ("int") int-type)
    (type ("bool") bool-type)
    (type ("void") void-type)
    (type ("(" (separated-list type "*") "->" type ")") proc-type)
    (type ("listof" type) list-type)
    (type (identifier) class-type) ;; new for typed oo
    ))

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda ()
    (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

(define type->class-name
  (lambda (ty)
    (cases type
           ty
           (class-type (name) name)
           (else (eopl:error 'type->class-name
                             "Not a class type: ~s"
                             ty)))))

(define class-type?
  (lambda (ty) (cases type ty (class-type (name) #t) (else #f))))

(define type-to-external-form
  (lambda (ty)
    (cases type
           ty
           (int-type () 'int)
           (bool-type () 'bool)
           (void-type () 'void)
           (class-type (name) name)
           (list-type (ty) (list 'listof (type-to-external-form ty)))
           (proc-type
            (arg-types result-type)
            (append (formal-types-to-external-form arg-types)
                    '(->)
                    (list (type-to-external-form result-type)))))))

(define formal-types-to-external-form
  (lambda (types)
    (if (null? types)
        '()
        (if (null? (cdr types))
            (list (type-to-external-form (car types)))
            (cons (type-to-external-form (car types))
                  (cons '*
                        (formal-types-to-external-form
                         (cdr types))))))))
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
    (map
     (lambda (m-decl)
       (cases method-decl
              m-decl
              (a-method-decl
               (result-type method-name vars var-types body)
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
           ;; interfaces don't affect runtime
           (an-interface-decl (interface-name method-decls) '())
           (a-class-decl
            (class-name super-name
                        interface-names
                        field-types
                        field-names
                        method-decls)
            (let ([field-names (append-field-names
                                (class->field-names
                                 (lookup-class super-name))
                                field-names)])
              (add-to-class-env!
               class-name
               (a-class super-name
                        field-names
                        (merge-method-envs
                         (class->method-env (lookup-class super-name))
                         (method-decls->method-env
                          method-decls
                          super-name
                          field-names)))))))))

;; append-field-names :  Listof(FieldName) * Listof(FieldName) -> Listof(FieldName)
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
                 (ref-val (ref reference?))
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

(define expval->ref
  (lambda (v)
    (cases expval
           v
           (ref-val (ref) ref)
           (else (expval-extractor-error 'reference v)))))

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
;;; static data structures
(define-datatype type-environment
                 type-environment?
                 (empty-tenv)
                 (extend-tenv (syms (list-of symbol?))
                              (vals (list-of type?))
                              (tenv type-environment?))
                 (extend-tenv-with-self-and-super
                  (self type?)
                  (super-name symbol?)
                  (saved-env type-environment?)))

(define init-tenv
  (lambda ()
    (extend-tenv '(true false)
                 (list (bool-type) (bool-type))
                 (empty-tenv))))

(define apply-tenv
  (lambda (env search-sym)
    (cases
     type-environment
     env
     (empty-tenv
      ()
      (eopl:error 'apply-tenv "No type found for ~s" search-sym))
     (extend-tenv (bvars types saved-env)
                  (cond
                    [(location search-sym bvars)
                     =>
                     (lambda (n) (list-ref types n))]
                    [else (apply-tenv saved-env search-sym)]))
     (extend-tenv-with-self-and-super
      (self-name super-name saved-env)
      (case search-sym
        [(%self) self-name]
        [(%super) super-name]
        [else (apply-tenv saved-env search-sym)])))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; static classes

(define method-tenv?
  (list-of (lambda (p)
             (and (pair? p) (symbol? (car p)) (type? (cadr p))))))

(define-datatype
 static-class
 static-class?
 (a-static-class (super-name (maybe identifier?))
                 (interface-names (list-of identifier?))
                 (field-names (list-of identifier?))
                 (field-types (list-of type?))
                 (method-tenv method-tenv?))
 (an-interface (method-tenv method-tenv?)))

;; method-tenv * id -> (maybe type)
(define maybe-find-method-type
  (lambda (m-env id)
    (cond
      [(assq id m-env)
       =>
       cadr]
      [else #f])))

;; class-name * id -> type OR fail
(define find-method-type
  (lambda (class-name id)
    (let ([m (maybe-find-method-type
              (static-class->method-tenv
               (lookup-static-class class-name))
              id)])
      (if m
          m
          (eopl:error 'find-method
                      "unknown method ~s in class ~s"
                      id
                      class-name)))))

;;;;;;;;;;;;;;;; the static class environment ;;;;;;;;;;;;;;;;

;; the-static-class-env will look like ((class-name static-class) ...)

(define the-static-class-env '())

(define is-static-class?
  (lambda (name) (assq name the-static-class-env)))

(define lookup-static-class
  (lambda (name)
    (cond
      [(assq name the-static-class-env)
       =>
       (lambda (pair) (cadr pair))]
      [else
       (eopl:error 'lookup-static-class "Unknown class: ~s" name)])))

(define empty-the-static-class-env!
  (lambda () (set! the-static-class-env '())))

(define add-static-class-binding!
  (lambda (name sc)
    (set! the-static-class-env
          (cons (list name sc) the-static-class-env))))

;;;;;;;;;;;;;;;; class declarations, etc. ;;;;;;;;;;;;;;;;

;; first, pull out all the types and put them in
;; the-static-class-env.

;; initialize-static-class-env! : Listof(ClassDecl) -> Unspecified
(define initialize-static-class-env!
  (lambda (c-decls)
    (empty-the-static-class-env!)
    (add-static-class-binding! 'object
                               (a-static-class #f '() '() '() '()))
    (for-each add-class-decl-to-static-class-env! c-decls)))

;; add-class-decl-to-static-class-env! : ClassDecl -> Unspecified
(define add-class-decl-to-static-class-env!
  (lambda (c-decl)
    (cases
     class-decl
     c-decl
     (an-interface-decl
      (i-name abs-m-decls)
      (let ([m-tenv (abs-method-decls->method-tenv abs-m-decls)])
        (check-no-dups! (map car m-tenv) i-name)
        (add-static-class-binding! i-name (an-interface m-tenv))))
     (a-class-decl
      (c-name s-name i-names f-types f-names m-decls)
      (let ([i-names (append (static-class->interface-names
                              (lookup-static-class s-name))
                             i-names)]
            [f-names (append-field-names
                      (static-class->field-names
                       (lookup-static-class s-name))
                      f-names)]
            [f-types (append (static-class->field-types
                              (lookup-static-class s-name))
                             f-types)]
            [method-tenv
             (let ([local-method-tenv
                    (method-decls->method-tenv m-decls)])
               (check-no-dups! (map car local-method-tenv) c-name)
               (merge-method-tenvs (static-class->method-tenv
                                    (lookup-static-class s-name))
                                   local-method-tenv))])
        (check-no-dups! i-names c-name)
        (check-no-dups! f-names c-name)
        (check-for-initialize! method-tenv c-name)
        (add-static-class-binding! c-name
                                   (a-static-class s-name
                                                   i-names
                                                   f-names
                                                   f-types
                                                   method-tenv)))))))

(define abs-method-decls->method-tenv
  (lambda (abs-m-decls)
    (map (lambda (abs-m-decl)
           (cases abstract-method-decl
                  abs-m-decl
                  (an-abstract-method-decl
                   (result-type m-name arg-ids arg-types)
                   (list m-name (proc-type arg-types result-type)))))
         abs-m-decls)))

(define method-decls->method-tenv
  (lambda (m-decls)
    (map (lambda (m-decl)
           (cases method-decl
                  m-decl
                  (a-method-decl
                   (result-type m-name arg-ids arg-types body)
                   (list m-name (proc-type arg-types result-type)))))
         m-decls)))

;; new methods override old ones.
(define merge-method-tenvs
  (lambda (super-tenv new-tenv) (append new-tenv super-tenv)))

(define check-for-initialize!
  (lambda (method-tenv class-name)
    (when (not (maybe-find-method-type method-tenv 'initialize))
      (eopl:error 'check-for-initialize!
                  "no initialize method in class ~s"
                  class-name))))

;;;;;;;;;;;;;;;; selectors ;;;;;;;;;;;;;;;;

(define static-class->super-name
  (lambda (sc)
    (cases static-class
           sc
           (a-static-class (super-name interface-names
                                       field-names
                                       field-types
                                       method-types)
                           super-name)
           (else (report-static-class-extractor-error 'super-name
                                                      sc)))))

(define static-class->interface-names
  (lambda (sc)
    (cases static-class
           sc
           (a-static-class (super-name interface-names
                                       field-names
                                       field-types
                                       method-types)
                           interface-names)
           (else (report-static-class-extractor-error 'interface-names
                                                      sc)))))

(define static-class->field-names
  (lambda (sc)
    (cases static-class
           sc
           (a-static-class (super-name interface-names
                                       field-names
                                       field-types
                                       method-types)
                           field-names)
           (else (report-static-class-extractor-error 'field-names
                                                      sc)))))

(define static-class->field-types
  (lambda (sc)
    (cases static-class
           sc
           (a-static-class (super-name interface-names
                                       field-names
                                       field-types
                                       method-types)
                           field-types)
           (else (report-static-class-extractor-error 'field-types
                                                      sc)))))

(define static-class->method-tenv
  (lambda (sc)
    (cases
     static-class
     sc
     (a-static-class
      (super-name interface-names field-names field-types method-tenv)
      method-tenv)
     (an-interface (method-tenv) method-tenv))))

(define report-static-class-extractor-error
  (lambda (sym sc)
    (eopl:error 'static-class-extractors
                "can't take ~s of interface ~s"
                sym
                sc)))

;; Listof(SchemeVal) * SchemeVal -> Unspecified
(define check-no-dups!
  (lambda (lst blamee)
    (let loop ([rest lst])
      (cond
        [(null? rest) #t]
        [(memv (car rest) (cdr rest))
         (eopl:error 'check-no-dups!
                     "duplicate found among ~s in class ~s"
                     lst
                     blamee)]
        [else (loop (cdr rest))]))))

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
;;; checker
;; type-of-program : Program -> Type
(define type-of-program
  (lambda (pgm)
    (cases program
           pgm
           (a-program (class-decls exp1)
                      (initialize-static-class-env! class-decls)
                      (for-each check-class-decl! class-decls)
                      (type-of exp1 (init-tenv))))))

;; type-of : Exp -> Tenv
(define type-of
  (lambda (exp tenv)
    (cases
     expression
     exp
     (const-exp (num) (int-type))
     (var-exp (var) (apply-tenv tenv var))
     (diff-exp (exp1 exp2)
               (let ([type1 (type-of exp1 tenv)]
                     [type2 (type-of exp2 tenv)])
                 (check-equal-type! type1 (int-type) exp1)
                 (check-equal-type! type2 (int-type) exp2)
                 (int-type)))
     (sum-exp (exp1 exp2)
              (let ([type1 (type-of exp1 tenv)]
                    [type2 (type-of exp2 tenv)])
                (check-equal-type! type1 (int-type) exp1)
                (check-equal-type! type2 (int-type) exp2)
                (int-type)))
     (zero?-exp (exp1)
                (let ([type1 (type-of exp1 tenv)])
                  (check-equal-type! type1 (int-type) exp1)
                  (bool-type)))
     (if-exp (test-exp true-exp false-exp)
             (let ([test-type (type-of test-exp tenv)]
                   [true-type (type-of true-exp tenv)]
                   [false-type (type-of false-exp tenv)])
               ;; these tests either succeed or raise an error
               (check-equal-type! test-type (bool-type) test-exp)
               (check-equal-type! true-type false-type exp)
               true-type))
     (let-exp
      (ids rands body)
      (let ([new-tenv
             (extend-tenv ids (types-of-exps rands tenv) tenv)])
        (type-of body new-tenv)))
     (proc-exp
      (bvars bvar-types body)
      (let ([result-type
             (type-of body (extend-tenv bvars bvar-types tenv))])
        (proc-type bvar-types result-type)))
     (call-exp (rator rands)
               (let ([rator-type (type-of rator tenv)]
                     [rand-types (types-of-exps rands tenv)])
                 (type-of-call rator-type rand-types rands exp)))
     (letrec-exp
      (proc-result-types proc-names
                         bvarss
                         bvar-typess
                         proc-bodies
                         letrec-body)
      (let ([tenv-for-letrec-body
             (extend-tenv
              proc-names
              (map proc-type bvar-typess proc-result-types)
              tenv)])
        (for-each
         (lambda (proc-result-type bvar-types bvars proc-body)
           (let ([proc-body-type
                  (type-of proc-body
                           (extend-tenv bvars
                                        bvar-types
                                        tenv-for-letrec-body))]) ;; !!
             (check-equal-type! proc-body-type
                                proc-result-type
                                proc-body)))
         proc-result-types
         bvar-typess
         bvarss
         proc-bodies)
        (type-of letrec-body tenv-for-letrec-body)))
     (begin-exp
      (exp1 exps)
      (letrec ([type-of-begins
                (lambda (e1 es)
                  (let ([v1 (type-of e1 tenv)])
                    (if (null? es)
                        v1
                        (type-of-begins (car es) (cdr es)))))])
        (type-of-begins exp1 exps)))
     (assign-exp
      (id rhs)
      (check-is-subtype! (type-of rhs tenv) (apply-tenv tenv id) exp)
      (void-type))
     (list-exp
      (exp1 exps)
      (let ([type-of-car (type-of exp1 tenv)])
        (for-each
         (lambda (exp)
           (check-equal-type! (type-of exp tenv) type-of-car exp))
         exps)
        (list-type type-of-car)))
     ;; object stuff begins here
     (new-object-exp
      (class-name rands)
      (let ([arg-types (types-of-exps rands tenv)]
            [c (lookup-static-class class-name)])
        (cases
         static-class
         c
         (an-interface (method-tenv)
                       (report-cant-instantiate-interface class-name))
         (a-static-class
          (super-name i-names field-names field-types method-tenv)
          ;; check the call to initialize
          (type-of-call (find-method-type class-name 'initialize)
                        arg-types
                        rands
                        exp)
          ;; and return the class name as a type
          (class-type class-name)))))
     (self-exp () (apply-tenv tenv '%self))
     (method-call-exp (obj-exp method-name rands)
                      (let ([arg-types (types-of-exps rands tenv)]
                            [obj-type (type-of obj-exp tenv)])
                        (type-of-call (find-method-type
                                       (type->class-name obj-type)
                                       method-name)
                                      arg-types
                                      rands
                                      exp)))
     (super-call-exp
      (method-name rands)
      (let ([arg-types (types-of-exps rands tenv)]
            [obj-type (apply-tenv tenv '%self)])
        (type-of-call
         (find-method-type (apply-tenv tenv '%super) method-name)
         arg-types
         rands
         exp)))
     ;; this matches interp.scm:  interp.scm calls
     ;; object->class-name, which fails on a non-object, so we need
     ;; to make sure that obj-type is in fact a class type.
     ;; interp.scm calls is-subclass?, which never raises an error,
     ;; so we don't need to do anything with class-name here.
     (cast-exp (exp class-name)
               (let ([obj-type (type-of exp tenv)])
                 (if (class-type? obj-type)
                     (class-type class-name)
                     (report-bad-type-to-cast obj-type exp))))
     ;; instanceof in interp.scm behaves the same way as cast:  it
     ;; calls object->class-name on its argument, so we need to
     ;; check that the argument is some kind of object, but we
     ;; don't need to look at class-name at all.
     (instanceof-exp
      (exp class-name)
      (let ([obj-type (type-of exp tenv)])
        (if (class-type? obj-type)
            (bool-type)
            (report-bad-type-to-instanceof obj-type exp)))))))

(define report-cant-instantiate-interface
  (lambda (class-name)
    (eopl:error 'type-of-new-obj-exp
                "Can't instantiate interface ~s"
                class-name)))

(define types-of-exps
  (lambda (rands tenv) (map (lambda (exp) (type-of exp tenv)) rands)))

;; type-of-call : Type * Listof(Type) * Listof(Exp) -> Type
(define type-of-call
  (lambda (rator-type rand-types rands exp)
    (cases
     type
     rator-type
     (proc-type
      (arg-types result-type)
      (when (not (= (length arg-types) (length rand-types)))
        (report-wrong-number-of-arguments arg-types rand-types exp))
      (for-each check-is-subtype! rand-types arg-types rands)
      result-type)
     (else (report-rator-not-of-proc-type
            (type-to-external-form rator-type)
            exp)))))

(define report-rator-not-of-proc-type
  (lambda (external-form-rator-type exp)
    (eopl:error 'type-of-call
                "rator ~s is not of proc-type ~s"
                exp
                external-form-rator-type)))

(define report-wrong-number-of-arguments
  (lambda (arg-types rand-types exp)
    (eopl:error 'type-of-call
                "These are not the same: ~s and ~s in ~s"
                (map type-to-external-form arg-types)
                (map type-to-external-form rand-types)
                exp)))

;; check-class-decl! : ClassDecl -> Unspecified
(define check-class-decl!
  (lambda (c-decl)
    (cases class-decl
           c-decl
           (an-interface-decl (i-name abs-method-decls) #t)
           (a-class-decl
            (class-name super-name
                        i-names
                        field-types
                        field-names
                        method-decls)
            (let ([sc (lookup-static-class class-name)])
              (for-each (lambda (method-decl)
                          (check-method-decl!
                           method-decl
                           class-name
                           super-name
                           (static-class->field-names sc)
                           (static-class->field-types sc)))
                        method-decls))
            (for-each (lambda (i-name)
                        (check-if-implements! class-name i-name))
                      i-names)))))

;; check-method-decl! :
;;   MethodDecl * ClassName * ClassName * Listof(FieldName) * \Listof(Type)
;;    -> Unspecified
(define check-method-decl!
  (lambda (m-decl self-name s-name f-names f-types)
    (cases
     method-decl
     m-decl
     (a-method-decl
      (res-type m-name vars var-types body)
      (let ([tenv (extend-tenv
                   vars
                   var-types
                   (extend-tenv-with-self-and-super
                    (class-type self-name)
                    s-name
                    (extend-tenv f-names f-types (init-tenv))))])
        (let ([body-type (type-of body tenv)])
          (check-is-subtype! body-type res-type m-decl)
          (if (eqv? m-name 'initialize)
              #t
              (let ([maybe-super-type (maybe-find-method-type
                                       (static-class->method-tenv
                                        (lookup-static-class s-name))
                                       m-name)])
                (if maybe-super-type
                    (check-is-subtype! (proc-type var-types res-type)
                                       maybe-super-type
                                       body)
                    #t)))))))))

;; check-if-implements! : ClassName * InterfaceName -> Bool
(define check-if-implements!
  (lambda (c-name i-name)
    (cases
     static-class
     (lookup-static-class i-name)
     (a-static-class
      (s-name i-names f-names f-types m-tenv)
      (report-cant-implement-non-interface c-name i-name))
     (an-interface
      (method-tenv)
      (let ([class-method-tenv (static-class->method-tenv
                                (lookup-static-class c-name))])
        (for-each
         (lambda (method-binding)
           (let ([m-name (car method-binding)]
                 [m-type (cadr method-binding)])
             (let ([c-method-type (maybe-find-method-type
                                   class-method-tenv
                                   m-name)])
               (if c-method-type
                   (check-is-subtype! c-method-type m-type c-name)
                   (report-missing-method c-name i-name m-name)))))
         method-tenv))))))

(define report-cant-implement-non-interface
  (lambda (c-name i-name)
    (eopl:error 'check-if-implements
                "class ~s claims to implement non-interface ~s"
                c-name
                i-name)))

(define report-missing-method
  (lambda (c-name i-name i-m-name)
    (eopl:error 'check-if-implements
                "class ~s claims to implement ~s, missing method ~s"
                c-name
                i-name
                i-m-name)))

;;;;;;;;;;;;;;;; types ;;;;;;;;;;;;;;;;

(define check-equal-type!
  (lambda (t1 t2 exp)
    (if (equal? t1 t2)
        #t
        (eopl:error 'type-of
                    "Types didn't match: ~s != ~s in~%~s"
                    (type-to-external-form t1)
                    (type-to-external-form t2)
                    exp))))

;; check-is-subtype! : Type * Type * Exp -> Unspecified
(define check-is-subtype!
  (lambda (ty1 ty2 exp)
    (if (is-subtype? ty1 ty2)
        #t
        (report-subtype-failure (type-to-external-form ty1)
                                (type-to-external-form ty2)
                                exp))))

(define report-subtype-failure
  (lambda (external-form-ty1 external-form-ty2 exp)
    (eopl:error 'check-is-subtype!
                "~s is not a subtype of ~s in ~%~s"
                external-form-ty1
                external-form-ty2
                exp)))

;; need this for typing cast expressions
;; is-subtype? : Type * Type -> Bool
(define is-subtype?
  (lambda (ty1 ty2)
    (cases type
           ty1
           (class-type
            (name1)
            (cases type
                   ty2
                   (class-type (name2)
                               (statically-is-subclass? name1 name2))
                   (else #f)))
           (proc-type
            (args1 res1)
            (cases type
                   ty2
                   (proc-type (args2 res2)
                              (and (every2? is-subtype? args2 args1)
                                   (is-subtype? res1 res2)))
                   (else #f)))
           (else (equal? ty1 ty2)))))

(define andmap
  (lambda (pred lst1 lst2)
    (cond
      [(and (null? lst1) (null? lst2)) #t]
      [(or (null? lst1) (null? lst2)) #f] ; or maybe throw error
      [(pred (car lst1) (car lst2))
       (andmap pred (cdr lst1) (cdr lst2))]
      [else #f])))

(define every2? andmap)

;; statically-is-subclass? : ClassName * ClassName -> Bool
(define statically-is-subclass?
  (lambda (name1 name2)
    (or
     (eqv? name1 name2)
     (let ([super-name (static-class->super-name
                        (lookup-static-class name1))])
       (if super-name (statically-is-subclass? super-name name2) #f))
     (let ([interface-names (static-class->interface-names
                             (lookup-static-class name1))])
       (memv name2 interface-names)))))

(define report-bad-type-to-cast
  (lambda (type exp)
    (eopl:error 'bad-type-to-case
                "can't cast non-object; ~s had type ~s"
                exp
                (type-to-external-form type))))

(define report-bad-type-to-instanceof
  (lambda (type exp)
    (eopl:error 'bad-type-to-case
                "can't apply instanceof to non-object; ~s had type ~s"
                exp
                (type-to-external-form type))))

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
     (proc-exp (bvars types body)
               (proc-val (procedure bvars body env)))
     (call-exp (rator rands)
               (let ([proc (expval->proc (value-of rator env))]
                     [args (values-of-exps rands env)])
                 (apply-procedure proc args)))
     (letrec-exp
      (result-types p-names b-varss b-vartypess p-bodies letrec-body)
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
     ;; args need to be non-empty for type checker
     (list-exp (exp exps)
               (list-val (cons (value-of exp env)
                               (values-of-exps exps env))))
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
         (find-method (object->class-name obj) method-name)
         obj
         args)))
     (super-call-exp
      (method-name rands)
      (let ([args (values-of-exps rands env)]
            [obj (apply-env env '%self)])
        (apply-method
         (find-method (apply-env env '%super) method-name)
         obj
         args)))
     ;; new cases for typed-oo
     (cast-exp (exp c-name)
               (let ([obj (value-of exp env)])
                 (if (is-subclass? (object->class-name obj) c-name)
                     obj
                     (report-cast-error c-name obj))))
     (instanceof-exp
      (exp c-name)
      (let ([obj (value-of exp env)])
        (if (is-subclass? (object->class-name obj) c-name)
            (bool-val #t)
            (bool-val #f)))))))

(define report-cast-error
  (lambda (c-name obj)
    (eopl:error 'value-of
                "Can't cast object to type ~s:~%~s"
                c-name
                obj)))

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
;; exercise: add instrumentation to apply-method, like that for
;; apply-procedure.

(define values-of-exps
  (lambda (exps env) (map (lambda (exp) (value-of exp env)) exps)))

;; is-subclass? : ClassName * ClassName -> Bool
(define is-subclass?
  (lambda (c-name1 c-name2)
    (if (eqv? c-name1 c-name2)
        #t
        (let ([s-name (class->super-name (lookup-class c-name1))])
          (if s-name (is-subclass? s-name c-name2) #f)))))

;; store->readable : Listof(List(Ref,Expval))
;;                    -> Listof(List(Ref,Something-Readable))
(define store->readable
  (lambda (l)
    (map (lambda (p) (cons (car p) (expval->printable (cadr p)))) l)))

(define :e (lambda (str) (value-of-program (scan&parse str))))
(define :t (lambda (str) (type-of-program (scan&parse str))))

(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; test
(require rackunit)

(define str0
  "
  class c extends object
           field int s
           method void initialize(v : int)set s = v
           method void sets(v : int)set s = v
           method int gets()s
           method void testit()send self sets(13)

  let o = new c (11)
         t1 = 0
         t2 = 0
  in begin
      set t1 = send o gets();
      send o testit();
      set t2 = send o gets();
      list(t1,t2)
     end
  ")
(check-equal? (:e str0) (list-val (list (num-val 11) (num-val 13))))
(check-equal? (:t str0) (list-type (int-type)))

(define str1
  "
  class counter extends object
    field int count
    method void initialize()set count = 0
    method void countup()set count = +(count,1)
    method int getcount()count

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
(check-equal? (:e str1) (list-val (list (num-val 0) (num-val 1))))
(check-equal? (:t str1) (list-type (int-type)))

(define str2
  "
  class counter extends object
  field int count
   method void initialize()set count = 0
   method void countup()set count = +(count,1)
   method int getcount()count

class c1 extends object
   field int n
   field counter counter1
   method void initialize(a_counter : counter)
    begin
     set n = 0;
     set counter1 = a_counter
    end
   method void countup()
     begin
      send counter1 countup();
      set n = +(n,1)
     end
   method listof int getstate()list(n, send counter1 getcount())

let counter1 = new counter()
in let o1 = new c1(counter1)
       o2 = new c1(counter1)
in begin
     send o1 countup();
     send o2 countup();
     send o2 countup();
     list( send o1 getstate(),
           send o2 getstate())
   end
  ")
(check-equal?
 (:e str2)
 (list-val (list (list-val (list (num-val 1) (num-val 3)))
                 (list-val (list (num-val 2) (num-val 3))))))
(check-equal? (:t str2) (list-type (list-type (int-type))))

(define str3
  "
class c1 extends object
  field int ivar1
  method void initialize()set ivar1 = 1

class c2 extends c1
  field int ivar2
  method void initialize()
   begin
    super initialize();
    set ivar2 = 1
   end
  method void setiv1(n : int)set ivar1 = n
  method int getiv1()ivar1

let o = new c2 ()
    t1 = 0
in begin
       send o setiv1(33);
       send o getiv1()
   end
  ")
(check-equal? (:e str3) (num-val 33))
(check-equal? (:t str3) (int-type))

(define str4
  "
class oddeven extends object
  method int initialize()1
  method bool even(n : int) if zero?(n) then zero?(0) else send self odd(-(n,1))
  method bool odd(n : int) if zero?(n) then zero?(1) else send self even(-(n,1))

let o1 = new oddeven() in send o1 odd(13)
  ")
(check-equal? (:e str4) (bool-val #t))
(check-equal? (:t str4) (bool-type))

(define str5
  "
interface tree
  method int sum()

class interior_node extends object implements tree
  field tree left
  field tree right
  method void initialize(l : tree, r : tree)
   begin
    set left = l; set right = r
   end
  method int sum()+(send left sum(), send right sum())

class leaf_node extends object implements tree
  field int value
  method void initialize(v : int)set value = v
  method int sum()value

let o1 = new interior_node (
          new interior_node (
            new leaf_node(3),
            new leaf_node(4)),
          new leaf_node(5))
in send o1 sum()
  ")
(check-equal? (:e str5) (num-val 12))
(check-equal? (:t str5) (int-type))

(define str6
  "
interface tree
  method int sum()
  method bool equal(t : tree)

class interior_node extends object implements tree
  field tree left
  field tree right
  method void initialize(l : tree, r : tree)
   begin
    set left = l; set right = r
   end
  method tree getleft()left
  method tree getright()right
  method int sum()+(send left sum(), send right sum())
  method bool equal(t : tree)
    if instanceof t interior_node
     then if send left equal(send cast t interior_node getleft())
          then send right equal(send cast t interior_node getright())
          else false
     else false


class leaf_node extends object implements tree
  field int value
  method void initialize(v : int)set value = v
  method int sum()value
  method int getvalue()value
  method bool equal(t : tree)
   if instanceof t leaf_node
    then zero?(-(value, send cast t leaf_node getvalue()))
    else zero?(1)


let o1 = new interior_node (
          new interior_node (
            new leaf_node(3),
            new leaf_node(4)),
          new leaf_node(5))
in send o1 equal(o1)
  ")
(check-equal? (:e str6) (bool-val #t))
(check-equal? (:t str6) (bool-type))

(define str7
  "
class c1 extends object
 method int initialize () 1
class c2 extends object
 method int initialize () 2
let p = proc (o : c1) instanceof o c2 in (p new c1())
  ")
(check-equal? (:e str7) (bool-val #f))
(check-equal? (:t str7) (bool-type))

(define str8
  "
class c1 extends object
  method int initialize () 1
  method int get() 2

class c2 extends c1
  method int get() 3

let f = proc (o : c2) send cast o c1 get() in (f new c2())
  ")
(check-equal? (:e str8) (num-val 3))
(check-equal? (:t str8) (int-type))

(define str9
  "
  class c1 extends object
  method int initialize() 1
class c2 extends c1
  method int m1() 1
  method int m1() 2

  33
  ")
(check-equal? (:e str9) (num-val 33))
; (:t str9) ;should fail

(define str10
  "
class c1 extends object
  method int initialize ()1
  method int get()2

class c2 extends object
  method int initialize () 100

let f = proc (o : c2) if instanceof o c1 then 1 else 2 in (f new c2())
  ")
(check-equal? (:e str10) (num-val 2))
(check-equal? (:t str10) (int-type))

(define str11
  "
interface tree
  method int sum()
  method bool equal(t : tree)
  method bool equal_int(l : tree, r : tree)
  method bool equal_leaf(val : int)
  
class interior_node extends object implements tree
  field tree left
  field tree right
  method void initialize(l : tree, r : tree)
   begin
    set left = l; set right = r
   end
  method int sum() +(send left sum(), send right sum())
  method bool equal(t : tree) send t equal_int(left, right)
  method bool equal_int(l : tree, r : tree) 
     if send left equal(l)
     then send right equal(r)
     else zero?(1)  % false
     
  method bool equal_leaf(v : int) false
  
class leaf_node extends object implements tree
  field int value
  field bool false
  method void initialize(v : int) begin set value = v; set
                                      false=zero?(1) end
  method int sum()value
  method bool equal(t : tree) send t equal_leaf(value)
  method bool equal_int(l : tree, r : tree) false
  method bool equal_leaf(otherval : int) zero?(-(value, otherval))
  
let o1 = new interior_node (
          new interior_node (
            new leaf_node(3),   
            new leaf_node(4)),
          new leaf_node(5))
in send o1 equal(o1)
  ")
(check-equal? (:e str11) (bool-val #t))
(check-equal? (:t str11) (bool-type))