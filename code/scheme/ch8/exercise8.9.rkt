#lang eopl
(require rackunit)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Grammar
(define identifier?
  (lambda (exp) (and (symbol? exp) (not (eqv? exp 'lambda)))))

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define the-grammar
  '((program ((arbno module-definition) depends-on expression)
             a-program)
    (module-definition
     ("module" identifier "interface" interface "body" module-body)
     a-module-definition)
    (interface ("[" (arbno declaration) "]") simple-iface)
    (declaration (identifier ":" type) val-decl)
    (module-body (depends-on "[" (arbno definition) "]")
                 defns-module-body)
    (definition (identifier "=" expression) val-defn)
    (depends-on ("depends-on" (separated-list identifier ",") ";")
                depends-on-clause)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression)
                if-exp)
    (expression (identifier) var-exp)
    (expression ("let" identifier "=" expression "in" expression)
                let-exp)
    (expression ("proc" "(" identifier ":" type ")" expression)
                proc-exp)
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
    (expression ("from" identifier "take" identifier)
                qualified-var-exp)
    ; (type (identifier) named-type)
    ; (type ("from" identifier "take" identifier) qualified-type)
    (type ("int") int-type)
    (type ("bool") bool-type)
    (type ("(" type "->" type ")") proc-type)))

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda ()
    (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define atomic-type?
  (lambda (ty) (cases type ty (proc-type (ty1 ty2) #f) (else #t))))

(define proc-type?
  (lambda (ty) (cases type ty (proc-type (t1 t2) #t) (else #f))))

(define proc-type->arg-type
  (lambda (ty)
    (cases type
      ty
      (proc-type (arg-type result-type) arg-type)
      (else (eopl:error 'proc-type->arg-type
                        "Not a proc type: ~s"
                        ty)))))

(define proc-type->result-type
  (lambda (ty)
    (cases type
      ty
      (proc-type (arg-type result-type) result-type)
      (else (eopl:error 'proc-type->result-types
                        "Not a proc type: ~s"
                        ty)))))

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
      ;  (named-type (name) name)
      ;  (qualified-type (modname varname)
      ;                  (list 'from modname 'take varname))
      )))

;; maybe-lookup-module-in-list : Sym * Listof(Defn) -> Maybe(Defn)
(define maybe-lookup-module-in-list
  (lambda (name module-defs)
    (if (null? module-defs)
        #f
        (let ([name1 (module-definition->name (car module-defs))])
          (if (eqv? name1 name)
              (car module-defs)
              (maybe-lookup-module-in-list name
                                           (cdr module-defs)))))))

;; maybe-lookup-module-in-list : Sym * Listof(Defn) -> Defn OR Error
(define lookup-module-in-list
  (lambda (name module-defs)
    (cond
      [(maybe-lookup-module-in-list name module-defs)
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
      (a-module-definition (m-name m-type m-body) m-name))))

(define module-definition->interface
  (lambda (m-defn)
    (cases module-definition
      m-defn
      (a-module-definition (m-name m-type m-body) m-type))))

(define module-definition->body
  (lambda (m-defn)
    (cases module-definition
      m-defn
      (a-module-definition (m-name m-type m-body) m-body))))

(define val-decl?
  (lambda (decl) (cases declaration decl (val-decl (name ty) #t))))

(define decl->name
  (lambda (decl) (cases declaration decl (val-decl (name ty) name))))

(define decl->type
  (lambda (decl) (cases declaration decl (val-decl (name ty) ty))))

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

(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors
                "Looking for a ~s, found ~s"
                variant
                value)))

(define-datatype
  proc
  proc?
  (procedure (bvar symbol?) (body expression?) (env environment?)))

;;; module values
(define-datatype typed-module
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
  (extend-env (bvar symbol?) (bval expval?) (saved-env environment?))
  (extend-env-recursively (id symbol?)
                          (bvar symbol?)
                          (body expression?)
                          (saved-env environment?))
  (extend-env-with-module (m-name symbol?)
                          (m-val typed-module?)
                          (saved-env environment?)))

(define apply-env
  (lambda (env search-sym)
    (cases
        environment
      env
      (empty-env
       ()
       (eopl:error 'apply-env "No value binding for ~s" search-sym))
      (extend-env (bvar bval saved-env)
                  (if (eqv? search-sym bvar)
                      bval
                      (apply-env saved-env search-sym)))
      (extend-env-recursively (id bvar body saved-env)
                              (if (eqv? search-sym id)
                                  (proc-val (procedure bvar body env))
                                  (apply-env saved-env search-sym)))
      (extend-env-with-module (m-name m-val saved-env)
                              (apply-env saved-env search-sym)))))

;; lookup-module-name-in-env : Sym * Env -> Typed-Module
(define lookup-module-name-in-env
  (lambda (m-name env)
    (cases environment
      env
      (empty-env ()
                 (eopl:error 'lookup-module-name-in-env
                             "No module binding for ~s"
                             m-name))
      (extend-env (bvar bval saved-env)
                  (lookup-module-name-in-env m-name saved-env))
      (extend-env-recursively
       (id bvar body saved-env)
       (lookup-module-name-in-env m-name saved-env))
      (extend-env-with-module
       (m-name1 m-val saved-env)
       (if (eqv? m-name1 m-name)
           m-val
           (lookup-module-name-in-env m-name saved-env))))))

;; lookup-qualified-var-in-env : Sym * Sym * Env -> ExpVal
(define lookup-qualified-var-in-env
  (lambda (m-name var-name env)
    (let ([m-val (lookup-module-name-in-env m-name env)])
      ; (pretty-print m-val)
      (cases
          typed-module
        m-val
        (simple-module (bindings) (apply-env bindings var-name))
        ;  (proc-module
        ;   (bvar body saved-env)
        ;   (eopl:error
        ;    'lookup-qualified-var
        ;    "can't retrieve variable from ~s take ~s from proc module"
        ;    m-name
        ;    var-name))
        ))))

;;;Tenv
(define-datatype type-environment
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
    (let ([iface (lookup-module-name-in-tenv tenv m-name)])
      (cases interface
        iface
        (simple-iface
         (decls)
         (lookup-variable-name-in-decls var-name decls))))))

(define lookup-variable-name-in-tenv
  (lambda (tenv search-sym)
    (let ([maybe-answer
           (variable-name->maybe-binding-in-tenv tenv search-sym)])
      (if maybe-answer
          maybe-answer
          (raise-tenv-lookup-failure-error 'variable
                                           search-sym
                                           tenv)))))

(define lookup-module-name-in-tenv
  (lambda (tenv search-sym)
    (let ([maybe-answer
           (module-name->maybe-binding-in-tenv tenv search-sym)])
      (if maybe-answer
          maybe-answer
          (raise-tenv-lookup-failure-error 'module
                                           search-sym
                                           tenv)))))

(define apply-tenv lookup-variable-name-in-tenv)

(define raise-tenv-lookup-failure-error
  (lambda (kind var tenv)
    (eopl:pretty-print
     (list 'tenv-lookup-failure: (list 'missing: kind var) 'in: tenv))
    (eopl:error 'lookup-variable-name-in-tenv)))

(define lookup-variable-name-in-decls
  (lambda (var-name decls0)
    (let loop ([decls decls0])
      (cond
        [(null? decls)
         (raise-lookup-variable-in-decls-error! var-name decls0)]
        [(eqv? var-name (decl->name (car decls)))
         (decl->type (car decls))]
        [else (loop (cdr decls))]))))

(define raise-lookup-variable-in-decls-error!
  (lambda (var-name decls)
    (eopl:pretty-print (list 'lookup-variable-decls-failure:
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
                     (if (eqv? name search-sym) ty (recur saved-tenv)))
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
         (if (eqv? name search-sym) m-type (recur saved-tenv)))
        (else (recur (tenv->saved-tenv tenv)))))))

;; assumes tenv is non-empty.
(define tenv->saved-tenv
  (lambda (tenv)
    (cases
        type-environment
      tenv
      (empty-tenv ()
                  (eopl:error 'tenv->saved-tenv
                              "tenv->saved-tenv called on empty tenv"))
      (extend-tenv (name ty saved-tenv) saved-tenv)
      (extend-tenv-with-module (name m-type saved-tenv) saved-tenv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Checker
(define expand-type (lambda (ty tenv) ty))
(define expand-iface (lambda (m-name iface tenv) iface))

;; check-equal-type! : Type * Type * Exp -> Unspecified
(define check-equal-type!
  (lambda (ty1 ty2 exp)
    (when (not (equal? ty1 ty2))
      (report-unequal-types ty1 ty2 exp))))

;; report-unequal-types : Type * Type * Exp -> Unspecified
(define report-unequal-types
  (lambda (ty1 ty2 exp)
    (eopl:error 'check-equal-type!
                "Types didn't match: ~s != ~a in~%~a"
                (type-to-external-form ty1)
                (type-to-external-form ty2)
                exp)))

;;;;;;;;;;;;;;;; The Type Checker ;;;;;;;;;;;;;;;;

;; type-of : Exp * Tenv -> Type
(define type-of
  (lambda (exp tenv)
    (cases
        expression
      exp
      (const-exp (num) (int-type))
      (diff-exp (exp1 exp2)
                (let ([type1 (type-of exp1 tenv)]
                      [type2 (type-of exp2 tenv)])
                  (check-equal-type! type1 (int-type) exp1)
                  (check-equal-type! type2 (int-type) exp2)
                  (int-type)))
      (zero?-exp (exp1)
                 (let ([type1 (type-of exp1 tenv)])
                   (check-equal-type! type1 (int-type) exp1)
                   (bool-type)))
      (if-exp (exp1 exp2 exp3)
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
       (lookup-qualified-var-in-tenv m-name var-name tenv))
      (let-exp (var exp1 body)
               (let ([rhs-type (type-of exp1 tenv)])
                 (type-of body (extend-tenv var rhs-type tenv))))
      (proc-exp
       (bvar bvar-type body)
       (let ([expanded-bvar-type (expand-type bvar-type tenv)])
         (let ([result-type
                (type-of body
                         (extend-tenv bvar expanded-bvar-type tenv))])
           (proc-type expanded-bvar-type result-type))))
      (call-exp
       (rator rand)
       (let ([rator-type (type-of rator tenv)]
             [rand-type (type-of rand tenv)])
         (cases
             type
           rator-type
           (proc-type (arg-type result-type)
                      (begin
                        (check-equal-type! arg-type rand-type rand)
                        result-type))
           (else (eopl:error
                  'type-of
                  "Rator not a proc type:~%~s~%had rator type ~s"
                  rator
                  (type-to-external-form rator-type))))))
      (letrec-exp
       (proc-result-type proc-name
                         bvar
                         bvar-type
                         proc-body
                         letrec-body)
       (let ([tenv-for-letrec-body
              (extend-tenv
               proc-name
               (expand-type (proc-type bvar-type proc-result-type)
                            tenv)
               tenv)])
         (let ([proc-result-type (expand-type proc-result-type tenv)]
               [proc-body-type
                (type-of proc-body
                         (extend-tenv bvar
                                      (expand-type bvar-type tenv)
                                      tenv-for-letrec-body))])
           (check-equal-type! proc-body-type
                              proc-result-type
                              proc-body)
           (type-of letrec-body tenv-for-letrec-body)))))))

(define init-tenv
  (lambda ()
    (extend-tenv 'true
                 (bool-type)
                 (extend-tenv 'false (bool-type) (empty-tenv)))))

;; type-of-program : Program -> Type
(define type-of-program
  (lambda (pgm)
    (cases
        program
      pgm
      (a-program
       (module-defs depends body)
       (let ([tenv (add-module-defns-to-tenv module-defs (init-tenv))])
         (let ([tenv (filter-depends-of-tenv depends tenv)])
           (eopl:pretty-print tenv)
           (type-of body tenv)))))))

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
           (let ([actual-iface (interface-of m-body tenv)])
             (if (<:-iface actual-iface expected-iface tenv)
                 (let ([new-tenv (extend-tenv-with-module
                                  m-name
                                  expected-iface
                                  tenv)])
                   (add-module-defns-to-tenv (cdr defns) new-tenv))
                 (report-module-doesnt-satisfy-iface
                  m-name
                  expected-iface
                  actual-iface))))))))

(define filter-depends-of-tenv
  (lambda (depends tenv)
    (cases
        depends-on
      depends
      (depends-on-clause
       (m-names)
       (let loop ([tenv tenv])
         (cases
             type-environment
           tenv
           (empty-tenv () tenv)
           (extend-tenv (name ty saved-tenv)
                        (extend-tenv name ty (loop saved-tenv)))
           (extend-tenv-with-module
            (name m-type saved-tenv)
            (if (memq name m-names)
                (extend-tenv-with-module name m-type (loop saved-tenv))
                (loop saved-tenv)))))))))

;; interface-of : ModuleBody * Tenv -> Iface
(define interface-of
  (lambda (m-body tenv)
    (cases module-body
      m-body
      (defns-module-body
        (depends defns)
        (let ([tenv (filter-depends-of-tenv depends tenv)])
          (simple-iface (defns-to-decls defns tenv)))))))

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
        (cases definition
          (car defns)
          (val-defn
           (var-name exp)
           (let ([ty (type-of exp tenv)])
             (let ([new-env (extend-tenv var-name ty tenv)])
               (cons (val-decl var-name ty)
                     (defns-to-decls (cdr defns) new-env)))))))))

(define report-module-doesnt-satisfy-iface
  (lambda (m-name expected-type actual-type)
    (eopl:pretty-print (list 'error-in-defn-of-module:
                             m-name
                             'expected-type:
                             expected-type
                             'actual-type:
                             actual-type))
    (eopl:error 'type-of-module-defn)))

;; <:-iface : Iface * Iface * Tenv -> Bool
(define <:-iface
  (lambda (iface1 iface2 tenv)
    (cases interface
      iface1
      (simple-iface
       (decls1)
       (cases interface
         iface2
         (simple-iface (decls2)
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
             (and (equal? (decl->type (car decls1))
                          (decl->type (car decls2)))
                  (<:-decls (cdr decls1) (cdr decls2) tenv))
             (<:-decls (cdr decls1) decls2 tenv)))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter
(define init-env
  (lambda ()
    (extend-env 'true
                (bool-val #t)
                (extend-env 'false (bool-val #f) (empty-env)))))

;; value-of-program : Program -> Expval
(define value-of-program
  (lambda (pgm)
    (cases
        program
      pgm
      (a-program
       (module-defs depends body)
       (let ([env (add-module-defns-to-env module-defs (init-env))])
         (let ([env (filter-depends-of-env depends env)])
            (eopl:pretty-print env)
           (value-of body env)))))))

;; add-module-defns-to-env : Listof(Defn) * Env -> Env
(define add-module-defns-to-env
  (lambda (defs env)
    (if (null? defs)
        env
        (cases module-definition
          (car defs)
          (a-module-definition
           (m-name iface m-body)
           (let ([env  (extend-env-with-module
                        m-name
                        (value-of-module-body m-body env)
                        env)])
             (add-module-defns-to-env (cdr defs) env)))))))

(define filter-depends-of-env
  (lambda (depends env)
    (cases
        depends-on
      depends
      (depends-on-clause
       (m-names)
       (let loop ([env env])
         (cases
             environment
           env
           (empty-env () env)
           (extend-env (var val saved-env)
                       (extend-env var val (loop saved-env)))
           (extend-env-recursively (id bvar body saved-env)
                                   (extend-env-recursively id bvar body
                                                           (loop saved-env)))
           (extend-env-with-module
            (name val saved-env)
            (if (memq name m-names)
                (extend-env-with-module name val (loop saved-env))
                (loop saved-env)))))))))

;; value-of-module-body : ModuleBody * Env -> TypedModule
(define value-of-module-body
  (lambda (m-body env)
    (cases module-body
      m-body
      (defns-module-body
        (depends defns)
        (simple-module
         (defns-to-env defns
           (filter-depends-of-env depends env)))))))

(define raise-cant-apply-non-proc-module!
  (lambda (rator-val)
    (eopl:error 'value-of-module-body
                "can't apply non-proc-module-value ~s"
                rator-val)))

;; defns-to-env : Listof(Defn) * Env -> Env
(define defns-to-env
  (lambda (defns env)
    (if (null? defns)
        (empty-env) ; we're making a little environment
        (cases definition
          (car defns)
          (val-defn
           (var exp)
           (let ([val (value-of exp env)])
             ;; new environment for subsequent definitions
             (let ([new-env (extend-env var val env)])
               (extend-env var
                           val
                           (defns-to-env (cdr defns)
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
       (lookup-qualified-var-in-env m-name var-name env))
      (diff-exp (exp1 exp2)
                (let ([val1 (expval->num (value-of exp1 env))]
                      [val2 (expval->num (value-of exp2 env))])
                  (num-val (- val1 val2))))
      (zero?-exp (exp1)
                 (let ([val1 (expval->num (value-of exp1 env))])
                   (if (zero? val1) (bool-val #t) (bool-val #f))))
      (if-exp (exp0 exp1 exp2)
              (if (expval->bool (value-of exp0 env))
                  (value-of exp1 env)
                  (value-of exp2 env)))
      (let-exp (var exp1 body)
               (let ([val (value-of exp1 env)])
                 (let ([new-env (extend-env var val env)])
                   ;; (eopl:pretty-print new-env)
                   (value-of body new-env))))
      (proc-exp (bvar ty body) (proc-val (procedure bvar body env)))
      (call-exp (rator rand)
                (let ([proc (expval->proc (value-of rator env))]
                      [arg (value-of rand env)])
                  (apply-procedure proc arg)))
      (letrec-exp
       (ty1 proc-name bvar ty2 proc-body letrec-body)
       (value-of
        letrec-body
        (extend-env-recursively proc-name bvar proc-body env))))))

;; apply-procedure : Proc * ExpVal -> ExpVal
(define apply-procedure
  (lambda (proc1 arg)
    (cases proc
      proc1
      (procedure
       (var body saved-env)
       (value-of body (extend-env var arg saved-env))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; test
(define :e (lambda (str) (value-of-program (scan&parse str))))
(define :t
  (lambda (str)
    (type-to-external-form (type-of-program (scan&parse str)))))

(define str0
  "module m1
      interface
        [a : int
         b : int
         c : int]
      body
        depends-on;
        [a = 33
         x = -(a,1) %x=32
         b = -(a,x) %b=1
         c = -(x,b) %c=31
        ]
  depends-on m1 ;
  let a = 10
  in -(-(from m1 take a,
         from m1 take b),
      a)")
(check-equal? (:e str0) (num-val 22))
(check-equal? (:t str0) 'int)

(define str1
  "module m1
      interface
       [u : int]
      body
       depends-on;
       [u = 33]
    depends-on;
    44")
(check-equal? (:e str1) (num-val 44))
(check-equal? (:t str1) 'int)


(define str2
  "module m1
      interface
        [u : int
         v : int]
      body
        depends-on;
        [v = 33
         u = 44]
   depends-on m1;
   from m1 take u")
(check-equal? (:e str2) (num-val 44))
; (:t str2) ; should fail

(define str3
  "module m1
      interface
        [u : int]
      body
        depends-on;
        [u = 44]
   module m2
      interface
       [v : int]
      body
       depends-on m1;
       [v = -(from m1 take u,
              11)]
    depends-on m1, m2;
   -(from m1 take u, from m2 take v)")
(check-equal? (:e str3) (num-val 11))
(check-equal? (:t str3) 'int)

(define str4
  " module m2
      interface
        [v : int]
      body
        depends-on;
        [v = -(from m1 take u,11)]
    module m1
      interface [u : int]
      body depends-on m1; [u = 44]
    depends-on m1, m2;
    -(from m1 take u, from m2 take v)")
; (:e str4) ;should fail
; (:t str4) ;should fail

(define str5
  "module m1
      interface
        [u : int]
      body
        depends-on;
        [u = 44]
   module m2
      interface
       [v : int]
      body
       depends-on;
       [v = -(from m1 take u,
              11)]
    depends-on;
    13")
; (:t str5) ;should fail
; (:e str5) ;should fail

(define str6
  "module m1
      interface
        [u : int]
      body
        depends-on;
        [u = 44]
   module m2
      interface
       [v : int]
      body
       depends-on m1;
       [v = -(from m1 take u,
              11)] %v=33
    module m3
      interface
       [w : int]
      body
       depends-on m1, m2;
       [w = -(from m1 take u,
              from m2 take v)] %w=11
    depends-on m1, m2, m3;
    let u = from m1 take u
    in let v = from m2 take v
       in let w = from m3 take w
          in zero?(-(u, -(v, -(0, w))))
    ")
(check-equal? (:e str6) (bool-val #t))
(check-equal? (:t str6) 'bool)

(define str7
  "module m1
      interface
        [u : int]
      body
        depends-on;
        [u = 44]
   module m2
      interface
       [v : int]
      body
       depends-on m1;
       [v = -(from m1 take u,
              11)]
    depends-on;
    from m2 take v")
; (:t str7) ;should fail
; (:e str7) ;should fail