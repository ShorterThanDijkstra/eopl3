#lang eopl
(require rackunit)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Grammar
(define identifier?
  (lambda (exp)
    (and (symbol? exp) (not (eqv? exp 'lambda)))))

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter
      (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define the-grammar
  '((program ((arbno module-definition)
              expression)
             a-program)
    (module-definition ("module" identifier
                                 "interface"
                                 interface
                                 "body"
                                 module-body)
                       a-module-definition)
    (interface ("[" (arbno declaration) "]")
               simple-iface)
    (declaration (identifier ":" type) val-decl)
    (module-body ("[" (arbno definition) "]")
                 defns-module-body)
    (module-body
     ("let" (arbno identifier "=" expression)
            "in"
            "["
            (arbno definition)
            "]")
     let-defns-module-body)
    (module-body
     ("letrec"
      (arbno
       type
       identifier
       "("
       (separated-list identifier ":" type ",")
       ")"
       "="
       expression)
      "in"
      "["
      (arbno definition)
      "]")
     letrec-defns-module-body)
    (definition (identifier "=" expression)
                val-defn)
    (expression (number) const-exp)
    (expression
     ("-" "(" expression "," expression ")")
     diff-exp)
    (expression ("zero?" "(" expression ")")
                zero?-exp)
    (expression ("if" expression
                      "then"
                      expression
                      "else"
                      expression)
                if-exp)
    (expression (identifier) var-exp)
    (expression
     ("let" (arbno identifier "=" expression)
            "in"
            expression)
     let-exp)
    (expression
     ("proc"
      "("
      (separated-list identifier ":" type ",")
      ")"
      expression)
     proc-exp)
    (expression
     ("(" expression (arbno expression) ")")
     call-exp)
    (expression
     ("letrec"
      (arbno
       type
       identifier
       "("
       (separated-list identifier ":" type ",")
       ")"
       "="
       expression)
      "in"
      expression)
     letrec-exp)
    (expression
     ("from" identifier "take" identifier)
     qualified-var-exp)
    ; (type (identifier) named-type)
    ; (type ("from" identifier "take" identifier) qualified-type)
    (type ("int") int-type)
    (type ("bool") bool-type)
    (type
     ("(" (separated-list type "*") "->" type ")")
     proc-type)))

(sllgen:make-define-datatypes the-lexical-spec
                              the-grammar)

(define show-the-datatypes
  (lambda ()
    (sllgen:list-define-datatypes the-lexical-spec
                                  the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec
                             the-grammar))

(define atomic-type?
  (lambda (ty)
    (cases type
           ty
           (proc-type (ty1 ty2) #f)
           (else #t))))

(define proc-type?
  (lambda (ty)
    (cases type
           ty
           (proc-type (t1 t2) #t)
           (else #f))))

(define proc-type->args-types
  (lambda (ty)
    (cases type
           ty
           (proc-type (args-types result-type)
                      args-types)
           (else (eopl:error
                  'proc-type->args-types
                  "Not a proc type: ~s"
                  ty)))))

(define proc-type->result-type
  (lambda (ty)
    (cases type
           ty
           (proc-type (args-types result-type)
                      result-type)
           (else (eopl:error
                  'proc-type->result-type
                  "Not a proc type: ~s"
                  ty)))))

(define type-to-external-form
  (lambda (ty)
    (cases
     type
     ty
     (int-type () 'int)
     (bool-type () 'bool)
     (proc-type
      (arg-types result-type)
      (if (null? arg-types)
          (type-to-external-form result-type)
          (let loop ([first (car arg-types)]
                     [rest (cdr arg-types)])
            (if (null? rest)
                (list (type-to-external-form
                       first)
                      '->
                      (type-to-external-form
                       result-type))
                (cons
                 (type-to-external-form first)
                 (cons '*
                       (loop (car rest)
                             (cdr rest))))))))
     ;  (named-type (name) name)
     ;  (qualified-type (modname varname)
     ;                  (list 'from modname 'take varname))
     )))

;; maybe-lookup-module-in-list : Sym * Listof(Defn) -> Maybe(Defn)
(define maybe-lookup-module-in-list
  (lambda (name module-defs)
    (if (null? module-defs)
        #f
        (let ([name1 (module-definition->name
                      (car module-defs))])
          (if (eqv? name1 name)
              (car module-defs)
              (maybe-lookup-module-in-list
               name
               (cdr module-defs)))))))

;; maybe-lookup-module-in-list : Sym * Listof(Defn) -> Defn OR Error
(define lookup-module-in-list
  (lambda (name module-defs)
    (cond
      [(maybe-lookup-module-in-list name
                                    module-defs)
       =>
       (lambda (mdef) mdef)]
      [else
       (eopl:error 'lookup-module-in-list
                   "unknown module ~s"
                   name)])))

(define module-definition->name
  (lambda (m-defn)
    (cases module-definition
           m-defn
           (a-module-definition
            (m-name m-type m-body)
            m-name))))

(define module-definition->interface
  (lambda (m-defn)
    (cases module-definition
           m-defn
           (a-module-definition
            (m-name m-type m-body)
            m-type))))

(define module-definition->body
  (lambda (m-defn)
    (cases module-definition
           m-defn
           (a-module-definition
            (m-name m-type m-body)
            m-body))))

(define val-decl?
  (lambda (decl)
    (cases declaration
           decl
           (val-decl (name ty) #t))))

(define decl->name
  (lambda (decl)
    (cases declaration
           decl
           (val-decl (name ty) name))))

(define decl->type
  (lambda (decl)
    (cases declaration
           decl
           (val-decl (name ty) ty))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Data Structure
;;; an expressed value is either a number, a boolean or a procval.
(define-datatype expval
                 expval?
                 (num-val (value number?))
                 (bool-val (boolean boolean?))
                 (proc-val (proc proc?)))

(define expval->num
  (lambda (v)
    (cases
     expval
     v
     (num-val (num) num)
     (else (expval-extractor-error 'num v)))))

(define expval->bool
  (lambda (v)
    (cases
     expval
     v
     (bool-val (bool) bool)
     (else (expval-extractor-error 'bool v)))))

(define expval->proc
  (lambda (v)
    (cases
     expval
     v
     (proc-val (proc) proc)
     (else (expval-extractor-error 'proc v)))))

(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors
                "Looking for a ~s, found ~s"
                variant
                value)))

(define-datatype
 proc
 proc?
 (procedure (vars (list-of identifier?))
            (body expression?)
            (saved-env environment?)))

;;; module values
(define-datatype
 typed-module
 typed-module?
 (simple-module (bindings environment?))
 ; (proc-module
 ;  (bvar symbol?)
 ;  (body module-body?)
 ;  (saved-env environment?))
 )

;;; environments
(define-datatype
 environment
 environment?
 (empty-env)
 (extend-env (bvar symbol?)
             (bval expval?)
             (saved-env environment?))
 (extend-env-recursively
  (p-names (list-of symbol?))
  (b-vars (list-of (list-of symbol?)))
  (p-bodies (list-of expression?))
  (saved-env environment?))
 (extend-env-with-module
  (m-name symbol?)
  (m-val typed-module?)
  (saved-env environment?)))

(define extend-env*
  (lambda (syms vals old-env)
    (if (null? syms)
        old-env
        (extend-env* (cdr syms)
                     (cdr vals)
                     (extend-env (car syms)
                                 (car vals)
                                 old-env)))))
(define apply-env
  (lambda (env search-sym)
    (cases
     environment
     env
     (empty-env ()
                (eopl:error
                 'apply-env
                 "No value binding for ~s"
                 search-sym))
     (extend-env
      (bvar bval saved-env)
      (if (eqv? search-sym bvar)
          bval
          (apply-env saved-env search-sym)))
     (extend-env-recursively
      (p-names b-vars p-bodies saved-env)
      (let loop ([p-names p-names]
                 [b-vars b-vars]
                 [p-bodies p-bodies])
        (cond
          [(null? p-names)
           (apply-env saved-env search-sym)]
          [(eqv? search-sym (car p-names))
           (proc-val (procedure (car b-vars)
                                (car p-bodies)
                                env))]
          [else
           (loop (cdr p-names)
                 (cdr b-vars)
                 (cdr p-bodies))])))
     (extend-env-with-module
      (m-name m-val saved-env)
      (apply-env saved-env search-sym)))))

;; lookup-module-name-in-env : Sym * Env -> Typed-Module
(define lookup-module-name-in-env
  (lambda (m-name env)
    (cases environment
           env
           (empty-env ()
                      (eopl:error
                       'lookup-module-name-in-env
                       "No module binding for ~s"
                       m-name))
           (extend-env (bvar bval saved-env)
                       (lookup-module-name-in-env
                        m-name
                        saved-env))
           (extend-env-recursively
            (id bvar body saved-env)
            (lookup-module-name-in-env m-name
                                       saved-env))
           (extend-env-with-module
            (m-name1 m-val saved-env)
            (if (eqv? m-name1 m-name)
                m-val
                (lookup-module-name-in-env
                 m-name
                 saved-env))))))

;; lookup-qualified-var-in-env : Sym * Sym * Env -> ExpVal
(define lookup-qualified-var-in-env
  (lambda (m-name var-name env)
    (let ([m-val (lookup-module-name-in-env m-name
                                            env)])
      ; (pretty-print m-val)
      (cases
       typed-module
       m-val
       (simple-module
        (bindings)
        (apply-env bindings var-name))
       ;  (proc-module
       ;   (bvar body saved-env)
       ;   (eopl:error
       ;    'lookup-qualified-var
       ;    "can't retrieve variable from ~s take ~s from proc module"
       ;    m-name
       ;    var-name))
       ))))

;;;Tenv
(define-datatype
 type-environment
 type-environment?
 (empty-tenv)
 (extend-tenv (bvar symbol?)
              (bval type?)
              (saved-tenv type-environment?))
 (extend-tenv-with-module
  (name symbol?)
  (interface interface?)
  (saved-tenv type-environment?)))

;; lookup-qualified-var-in-tenv : Sym * Sym * Tenv -> Type
(define lookup-qualified-var-in-tenv
  (lambda (m-name var-name tenv)
    (let ([iface (lookup-module-name-in-tenv
                  tenv
                  m-name)])
      (cases interface
             iface
             (simple-iface
              (decls)
              (lookup-variable-name-in-decls
               var-name
               decls))))))

(define lookup-variable-name-in-tenv
  (lambda (tenv search-sym)
    (let ([maybe-answer
           (variable-name->maybe-binding-in-tenv
            tenv
            search-sym)])
      (if maybe-answer
          maybe-answer
          (raise-tenv-lookup-failure-error
           'variable
           search-sym
           tenv)))))

(define lookup-module-name-in-tenv
  (lambda (tenv search-sym)
    (let ([maybe-answer
           (module-name->maybe-binding-in-tenv
            tenv
            search-sym)])
      (if maybe-answer
          maybe-answer
          (raise-tenv-lookup-failure-error
           'module
           search-sym
           tenv)))))

(define apply-tenv lookup-variable-name-in-tenv)

(define extend-tenv*
  (lambda (vars types tenv)
    (if (not (= (length vars) (length types)))
        (eopl:error 'extend-tenv*)
        (let loop ([vars vars] [types types])
          (if (null? vars)
              tenv
              (extend-tenv
               (car vars)
               (car types)
               (loop (cdr vars) (cdr types))))))))

(define raise-tenv-lookup-failure-error
  (lambda (kind var tenv)
    (eopl:pretty-print
     (list 'tenv-lookup-failure:
           (list 'missing: kind var)
           'in:
           tenv))
    (eopl:error 'lookup-variable-name-in-tenv)))

(define lookup-variable-name-in-decls
  (lambda (var-name decls0)
    (let loop ([decls decls0])
      (cond
        [(null? decls)
         (raise-lookup-variable-in-decls-error!
          var-name
          decls0)]
        [(eqv? var-name (decl->name (car decls)))
         (decl->type (car decls))]
        [else (loop (cdr decls))]))))

(define raise-lookup-variable-in-decls-error!
  (lambda (var-name decls)
    (eopl:pretty-print
     (list 'lookup-variable-decls-failure:
           (list 'missing-variable var-name)
           'in:
           decls))))

;; variable-name->maybe-binding-in-tenv : Tenv * Sym -> Maybe(Type)
(define variable-name->maybe-binding-in-tenv
  (lambda (tenv search-sym)
    (let recur ([tenv tenv])
      (cases
       type-environment
       tenv
       (empty-tenv () #f)
       (extend-tenv (name ty saved-tenv)
                    (if (eqv? name search-sym)
                        ty
                        (recur saved-tenv)))
       (else (recur (tenv->saved-tenv tenv)))))))

;; module-name->maybe-binding-in-tenv : Tenv * Sym -> Maybe(Iface)
(define module-name->maybe-binding-in-tenv
  (lambda (tenv search-sym)
    (let recur ([tenv tenv])
      (cases type-environment
             tenv
             (empty-tenv () #f)
             (extend-tenv-with-module
              (name m-type saved-tenv)
              (if (eqv? name search-sym)
                  m-type
                  (recur saved-tenv)))
             (else (recur (tenv->saved-tenv
                           tenv)))))))

;; assumes tenv is non-empty.
(define tenv->saved-tenv
  (lambda (tenv)
    (cases
     type-environment
     tenv
     (empty-tenv
      ()
      (eopl:error
       'tenv->saved-tenv
       "tenv->saved-tenv called on empty tenv"))
     (extend-tenv (name ty saved-tenv) saved-tenv)
     (extend-tenv-with-module
      (name m-type saved-tenv)
      saved-tenv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Checker
(define expand-type (lambda (ty tenv) ty))
(define expand-iface
  (lambda (m-name iface tenv) iface))

;; check-equal-type! : Type * Type * Exp -> Unspecified
(define check-equal-type!
  (lambda (ty1 ty2 exp)
    (when (not (equal? ty1 ty2))
      (report-unequal-types ty1 ty2 exp))))

;; report-unequal-types : Type * Type * Exp -> Unspecified
(define report-unequal-types
  (lambda (ty1 ty2 exp)
    (eopl:error
     'check-equal-type!
     "Types didn't match: ~s != ~a in~%~a"
     (type-to-external-form ty1)
     (type-to-external-form ty2)
     exp)))

;;;;;;;;;;;;;;;; The Type Checker ;;;;;;;;;;;;;;;;

(define report-rator-not-a-proc-type
  (lambda (rator-type rator)
    (eopl:error
     'type-of-expression
     "Rator not a proc type:~%~s~%had rator type ~s"
     rator
     (type-to-external-form rator-type))))

;; type-of : Exp * Tenv -> Type
(define type-of
  (lambda (exp tenv)
    (cases
     expression
     exp
     (const-exp (num) (int-type))
     (diff-exp
      (exp1 exp2)
      (let ([type1 (type-of exp1 tenv)]
            [type2 (type-of exp2 tenv)])
        (check-equal-type! type1 (int-type) exp1)
        (check-equal-type! type2 (int-type) exp2)
        (int-type)))
     (zero?-exp
      (exp1)
      (let ([type1 (type-of exp1 tenv)])
        (check-equal-type! type1 (int-type) exp1)
        (bool-type)))
     (if-exp
      (exp1 exp2 exp3)
      (let ([ty1 (type-of exp1 tenv)]
            [ty2 (type-of exp2 tenv)]
            [ty3 (type-of exp3 tenv)])
        (check-equal-type! ty1 (bool-type) exp1)
        (check-equal-type! ty2 ty3 exp)
        ty2))
     (var-exp (var) (apply-tenv tenv var))
     ;; lookup-qualified-var-in-tenv defined on page 285.
     (qualified-var-exp
      (m-name var-name)
      (lookup-qualified-var-in-tenv m-name
                                    var-name
                                    tenv))
     (let-exp
      (vars exps body)
      (let ([types (map (lambda (exp)
                          (type-of exp tenv))
                        exps)])
        (type-of body
                 (extend-tenv* vars types tenv))))
     (proc-exp
      (vars var-types body)
      (let ([result-type
             (type-of body
                      (extend-tenv* vars
                                    var-types
                                    tenv))])
        (proc-type var-types result-type)))
     (call-exp
      (rator rands)
      (let ([rator-type (type-of rator tenv)]
            [rand-types
             (map (lambda (rand)
                    (type-of rand tenv))
                  rands)])
        (cases type
               rator-type
               (proc-type
                (arg-types result-type)
                (begin
                  (check-equal-type! arg-types
                                     rand-types
                                     rands)
                  result-type))
               (else (report-rator-not-a-proc-type
                      rator-type
                      rator)))))
     (letrec-exp
      (p-result-types p-names
                      b-varss
                      b-varss-types
                      p-bodies
                      letrec-body)
      (let ([tenv-for-letrec-body
             (extend-tenv*
              p-names
              (map (lambda (b-vars-types
                            p-result-type)
                     (proc-type b-vars-types
                                p-result-type))
                   b-varss-types
                   p-result-types)
              tenv)])
        (let ([p-body-types
               (map (lambda (p-body b-vars
                                    b-vars-types)
                      (type-of
                       p-body
                       (extend-tenv*
                        b-vars
                        b-vars-types
                        tenv-for-letrec-body)))
                    p-bodies
                    b-varss
                    b-varss-types)])
          (check-equal-type! p-body-types
                             p-result-types
                             p-bodies)
          (type-of letrec-body
                   tenv-for-letrec-body)))))))

(define init-tenv
  (lambda ()
    (extend-tenv 'true
                 (bool-type)
                 (extend-tenv 'false
                              (bool-type)
                              (empty-tenv)))))

;; type-of-program : Program -> Type
(define type-of-program
  (lambda (pgm)
    (cases program
           pgm
           (a-program
            (module-defs body)
            (type-of body
                     (add-module-defns-to-tenv
                      module-defs
                      (init-tenv)))))))

;; add-module-defns-to-tenv : Listof(ModuleDefn) * Tenv -> Tenv
(define add-module-defns-to-tenv
  (lambda (defns tenv)
    (if (null? defns)
        tenv
        (cases
         module-definition
         (car defns)
         (a-module-definition
          (m-name expected-iface m-body)
          (let ([actual-iface
                 (interface-of m-body tenv)])
            (if (<:-iface actual-iface
                          expected-iface
                          tenv)
                (let ([new-tenv
                       (extend-tenv-with-module
                        m-name
                        expected-iface
                        tenv)])
                  (add-module-defns-to-tenv
                   (cdr defns)
                   new-tenv))
                (report-module-doesnt-satisfy-iface
                 m-name
                 expected-iface
                 actual-iface))))))))

;; interface-of : ModuleBody * Tenv -> Iface
(define interface-of
  (lambda (m-body tenv)
    (cases
     module-body
     m-body
     (defns-module-body
      (defns)
      (simple-iface (defns-to-decls defns tenv)))
     (let-defns-module-body
      (vars exps defns)
      (let ([tys (map (lambda (exp)
                        (type-of exp tenv))
                      exps)])
        (simple-iface
         (defns-to-decls
          defns
          (extend-tenv* vars tys tenv)))))
     (letrec-defns-module-body
      (p-result-types p-names
                      b-varss
                      b-varss-types
                      p-bodies
                      defns)
      (let ([tenv-for-letrec-body
             (extend-tenv*
              p-names
              (map (lambda (b-vars-types
                            p-result-type)
                     (proc-type b-vars-types
                                p-result-type))
                   b-varss-types
                   p-result-types)
              tenv)])
        (let ([p-body-types
               (map (lambda (p-body b-vars
                                    b-vars-types)
                      (type-of
                       p-body
                       (extend-tenv*
                        b-vars
                        b-vars-types
                        tenv-for-letrec-body)))
                    p-bodies
                    b-varss
                    b-varss-types)])
          (check-equal-type! p-body-types
                             p-result-types
                             p-bodies)
          (simple-iface
           (defns-to-decls
            defns
            tenv-for-letrec-body))))))))

;; defns-to-decls : Listof(Defn) * Tenv -> Listof(Decl)
;;
;; Convert defns to a set of declarations for just the names defined
;; in defns.  Do this in the context of tenv.  The tenv is extended
;; at every step, so we get the correct let* scoping
;;
(define defns-to-decls
  (lambda (defns tenv)
    (if (null? defns)
        '()
        (cases
         definition
         (car defns)
         (val-defn
          (var-name exp)
          (let ([ty (type-of exp tenv)])
            (let ([new-env (extend-tenv var-name
                                        ty
                                        tenv)])
              (cons (val-decl var-name ty)
                    (defns-to-decls
                     (cdr defns)
                     new-env)))))))))

(define report-module-doesnt-satisfy-iface
  (lambda (m-name expected-type actual-type)
    (eopl:pretty-print
     (list 'error-in-defn-of-module:
           m-name
           'expected-type:
           expected-type
           'actual-type:
           actual-type))
    (eopl:error 'type-of-module-defn)))

;; <:-iface : Iface * Iface * Tenv -> Bool
(define <:-iface
  (lambda (iface1 iface2 tenv)
    (cases
     interface
     iface1
     (simple-iface
      (decls1)
      (cases interface
             iface2
             (simple-iface
              (decls2)
              (<:-decls decls1 decls2 tenv)))))))

;; <:-decls : Listof(Decl) * Listof(Decl) * Tenv -> Bool
;;
;; s1 <: s2 iff s1 has at least as much stuff as s2, and in the same
;; order.  We walk down s1 until we find a declaration that declares
;; the same name as the first component of s2.  If we run off the
;; end of s1, then we fail.  As we walk down s1, we record any type
;; bindings in the tenv
;;
(define <:-decls
  (lambda (decls1 decls2 tenv)
    (cond
      [(null? decls2) #t]
      [(null? decls1) #f]
      [else
       (let ([name1 (decl->name (car decls1))]
             [name2 (decl->name (car decls2))])
         (if (eqv? name1 name2)
             (and (equal?
                   (decl->type (car decls1))
                   (decl->type (car decls2)))
                  (<:-decls (cdr decls1)
                            (cdr decls2)
                            tenv))
             (<:-decls (cdr decls1)
                       decls2
                       tenv)))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter
(define init-env
  (lambda ()
    (extend-env 'true
                (bool-val #t)
                (extend-env 'false
                            (bool-val #f)
                            (empty-env)))))
;; value-of-program : Program -> Expval
(define value-of-program
  (lambda (pgm)
    (cases program
           pgm
           (a-program
            (module-defs body)
            (let ([env (add-module-defns-to-env
                        module-defs
                        (init-env))])
              ; (eopl:pretty-print env)
              (value-of body env))))))

;; add-module-defns-to-env : Listof(Defn) * Env -> Env
(define add-module-defns-to-env
  (lambda (defs env)
    (if (null? defs)
        env
        (cases
         module-definition
         (car defs)
         (a-module-definition
          (m-name iface m-body)
          (add-module-defns-to-env
           (cdr defs)
           (extend-env-with-module
            m-name
            (value-of-module-body m-body env)
            env)))))))

;; value-of-module-body : ModuleBody * Env -> TypedModule
(define value-of-module-body
  (lambda (m-body env)
    (cases
     module-body
     m-body
     (defns-module-body
      (defns)
      (simple-module (defns-to-env defns env)))
     (let-defns-module-body
      (vars exps defns)
      (let ([vals (map (lambda (exp)
                         (value-of exp env))
                       exps)])
        (simple-module
         (defns-to-env
          defns
          (extend-env* vars vals env)))))
     (letrec-defns-module-body
      (p-result-types p-names
                      b-varss
                      b-varss-types
                      p-bodies
                      defns)
      (let ([new-env (extend-env-recursively
                      p-names
                      b-varss
                      p-bodies
                      env)])
        (simple-module
         (defns-to-env defns new-env)))))))

(define raise-cant-apply-non-proc-module!
  (lambda (rator-val)
    (eopl:error
     'value-of-module-body
     "can't apply non-proc-module-value ~s"
     rator-val)))

;; defns-to-env : Listof(Defn) * Env -> Env
(define defns-to-env
  (lambda (defns env)
    (if (null? defns)
        (empty-env) ; we're making a little environment
        (cases
         definition
         (car defns)
         (val-defn
          (var exp)
          (let ([val (value-of exp env)])
            ;; new environment for subsequent definitions
            (let ([new-env
                   (extend-env var val env)])
              (extend-env var
                          val
                          (defns-to-env
                           (cdr defns)
                           new-env)))))))))

;; value-of : Exp * Env -> ExpVal
(define value-of
  (lambda (exp env)

    (cases
     expression
     exp
     (const-exp (num) (num-val num))
     (var-exp (var) (apply-env env var))
     (qualified-var-exp
      (m-name var-name)
      (lookup-qualified-var-in-env m-name
                                   var-name
                                   env))
     (diff-exp (exp1 exp2)
               (let ([val1 (expval->num
                            (value-of exp1 env))]
                     [val2 (expval->num
                            (value-of exp2 env))])
                 (num-val (- val1 val2))))
     (zero?-exp
      (exp1)
      (let ([val1 (expval->num
                   (value-of exp1 env))])
        (if (zero? val1)
            (bool-val #t)
            (bool-val #f))))
     (if-exp (exp0 exp1 exp2)
             (if (expval->bool
                  (value-of exp0 env))
                 (value-of exp1 env)
                 (value-of exp2 env)))
     (let-exp
      (vars exps body)
      (let ([vals (map (lambda (exp1)
                         (value-of exp1 env))
                       exps)])
        (value-of body
                  (extend-env* vars vals env))))
     (proc-exp
      (bvars tys body)
      (proc-val (procedure bvars body env)))
     (call-exp
      (rator rands)
      (let ([proc (expval->proc
                   (value-of rator env))]
            [args (map (lambda (rand)
                         (value-of rand env))
                       rands)])
        (apply-procedure proc args)))
     (letrec-exp (tys1 p-names
                       b-varss
                       tys2
                       p-bodies
                       letrec-body)
                 (value-of letrec-body
                           (extend-env-recursively
                            p-names
                            b-varss
                            p-bodies
                            env))))))

;; apply-procedure : Proc * ExpVal -> ExpVal
(define apply-procedure
  (lambda (proc1 args)
    (cases
     proc
     proc1
     (procedure
      (vars body saved-env)
      (value-of
       body
       (extend-env* vars args saved-env))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; test
(define :e
  (lambda (str)
    (value-of-program (scan&parse str))))
(define :t
  (lambda (str)
    (type-to-external-form
     (type-of-program (scan&parse str)))))

(define str0
  "module m1
      interface
        [
         a : int
         b : int
         c : int
        ]
      body
        [
         a = 33
         x = -(a,1) %x=32
         b = -(a,x) %b=1
         c = -(x,b) %c=31
        ]
  let a = 10
  in -(-(from m1 take a,
         from m1 take b),
      a)")
(check-equal? (:e str0) (num-val 22))
(check-equal? (:t str0) 'int)

(define str1
  "module m1
      interface
       [u : bool]
      body
       [u = 33]
    44")
(check-equal? (:e str1) (num-val 44))
; (:t str1) ; should fail

(define str2
  "module m1
      interface
        [u : int
         v : int]
      body
        [v = 33
         u = 44]
   from m1 take u")
(check-equal? (:e str2) (num-val 44))
; (:t str2) ; should fail

(define str3
  "module m1
      interface
        [u : int]
      body
        [u = 44]
   module m2
      interface
       [v : int]
      body
       [v = -(from m1 take u,
              11)]
   -(from m1 take u, from m2 take v)")
(check-equal? (:e str3) (num-val 11))
(check-equal? (:t str3) 'int)

(define str4
  " module m2
      interface [v : int]
      body [v = -(from m1 take u,11)]
    module m1
      interface [u : int]
      body [u = 44]
    -(from m1 take u, from m2 take v)")
; (:e str4) ;should fail
; (:t str4) ;should fail

(define str5
  "
  module m1
    interface [f: (int * bool * (int * int * bool -> bool) -> int)]
    body [f = proc(x: int, y: bool, z: (int * int * bool -> bool))
                 if (z 10 11 true)
                 then 12
                 else if y
                      then x
                      else -(x, 1)]
   let z = proc(a: int, b: int, c: bool) if zero?(-(a, b)) then c else zero?(1)
   in (from m1 take f 13 false z)")
(check-equal? (:e str5) (num-val 12))
(check-equal? (:t str5) 'int)

(define str6
  "module m1
     interface [v: int]
     body [v = 0]
  proc() from m1 take v")
(check-equal?
 (:e str6)
 (proc-val
  (procedure
   '()
   (qualified-var-exp 'm1 'v)
   (extend-env-with-module
    'm1
    (simple-module
     (extend-env 'v (num-val 0) (empty-env)))
    (extend-env 'true
                (bool-val #t)
                (extend-env 'false
                            (bool-val #f)
                            (empty-env)))))))
(check-equal? (:t str6) 'int)

(define str7
  "module m1
     interface [f: (int * int -> bool)]
     body [f = proc(a: int, b: int)
                 zero?(-(a, b))]
  module m2
     interface [g: (int * int * (int * int -> bool) -> bool)]
     body [g =  proc(a: int, b: int, c:(int * int -> bool))
                  if (c a b) then false else true]
  let x = 11
       y = 13
       f = from m1 take f
       g = from m2 take g
   in (g x y f)")
(check-equal? (:e str7) (bool-val #t))
(check-equal? (:t str7) 'bool)

(define str8
  "module m1
     interface [add: (int * int -> int)]
     body [add = letrec int foo(a: int, b: int) = -(a, -(0, b))
                 in foo]
   module m2
     interface [mul: (int * int -> int)]
     body [mul = let add = from m1 take add
                 in letrec int foo(a: int, b: int) = if zero?(b) then 0 else (add a (foo a -(b, 1)))
                    in foo]
  let mul = from m2 take mul
  in letrec
       int fib(a: int, b: int, n: int) = if zero?(n) then b else (fib b -(a, -(0, b)) -(n, 1))
       int factk(n: int, k: (int -> int)) = if zero?(n) then (k 1) else (factk -(n, 1) proc(v0: int) (k (mul v0 n)))
     in -((factk 10 proc(x: int) x), (fib 0 1 10))")
(check-equal? (:t str8) 'int)
(check-equal? (:e str8) (num-val 3628711))

(define str9
  "module even-odd
  interface
     [even : (int -> bool)
      odd  : (int -> bool)]
  body
  letrec
    bool local-odd (x : int) = if zero?(x) then false else (local-even -(x, 1))
    bool local-even (x :int) = if zero?(x) then true else (local-odd -(x, 1))
  in
  [even = local-even
   odd = local-odd]
 (from even-odd take odd 114514)")
(check-equal? (:e str9) (bool-val #f))
(check-equal? (:t str9) 'bool)

