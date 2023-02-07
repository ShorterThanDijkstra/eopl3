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
  '((program ((arbno module-definition) expression) a-program)
    (module-definition
     ("module" identifier "interface" interface "body" module-body)
     a-module-definition)
    (interface ("[" (arbno declaration) "]") simple-iface)
    (declaration (identifier ":" type) val-decl)
    (declaration ("opaque" identifier) opaque-type-decl)
    (declaration ("transparent" identifier "=" type) transparent-type-decl)
    (module-body ("[" (arbno definition) "]") defns-module-body)
    (definition (identifier "=" expression) val-defn)
    (definition ("type" identifier "=" type) type-defn)
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
    (expression ("from" identifier "take" identifier) qualified-var-exp)
    (type (identifier) named-type)
    (type ("from" identifier "take" identifier) qualified-type)
    (type ("int") int-type)
    (type ("bool") bool-type)
    (type ("(" type "->" type ")") proc-type)))

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse (sllgen:make-string-parser the-lexical-spec the-grammar))

(define atomic-type?
  (lambda (ty) (cases type ty (proc-type (ty1 ty2) #f) (else #t))))

(define proc-type?
  (lambda (ty) (cases type ty (proc-type (t1 t2) #t) (else #f))))

(define proc-type->arg-type
  (lambda (ty)
    (cases type
      ty
      (proc-type (arg-type result-type) arg-type)
      (else (eopl:error 'proc-type->arg-type "Not a proc type: ~s" ty)))))

(define proc-type->result-type
  (lambda (ty)
    (cases
        type
      ty
      (proc-type (arg-type result-type) result-type)
      (else (eopl:error 'proc-type->result-types "Not a proc type: ~s" ty)))))

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
      (named-type (name) name)
      (qualified-type (modname varname)
                      (list 'from modname 'take varname))
      )))

;; maybe-lookup-module-in-list : Sym * Listof(Defn) -> Maybe(Defn)
(define maybe-lookup-module-in-list
  (lambda (name module-defs)
    (if (null? module-defs)
        #f
        (let ([name1 (module-definition->name (car module-defs))])
          (if (eqv? name1 name)
              (car module-defs)
              (maybe-lookup-module-in-list name (cdr module-defs)))))))

;; maybe-lookup-module-in-list : Sym * Listof(Defn) -> Defn OR Error
(define lookup-module-in-list
  (lambda (name module-defs)
    (cond
      [(maybe-lookup-module-in-list name module-defs)
       =>
       (lambda (mdef) mdef)]
      [else (eopl:error 'lookup-module-in-list "unknown module ~s" name)])))

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
  (lambda (decl)
    (cases declaration decl
      (val-decl (name ty) #t)
      (else #f))))

(define transparent-type-decl?
  (lambda (decl)
    (cases declaration decl
      (transparent-type-decl (name ty) #t)
      (else #f))))

(define opaque-type-decl?
  (lambda (decl)
    (cases declaration decl
      (opaque-type-decl (name) #t)
      (else #f))))

(define decl->name
  (lambda (decl)
    (cases declaration decl
      (opaque-type-decl (name) name)
      (transparent-type-decl (name ty) name)
      (val-decl (name ty) name))))

(define decl->type
  (lambda (decl)
    (cases declaration decl
      (transparent-type-decl (name ty) ty)
      (val-decl (name ty) ty)
      (opaque-type-decl (name)
                        (eopl:error 'decl->type
                                    "can't take type of abstract type declaration ~s"
                                    decl)))))
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
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s" variant value)))

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
      (empty-env () (eopl:error 'apply-env "No value binding for ~s" search-sym))
      (extend-env
       (bvar bval saved-env)
       (if (eqv? search-sym bvar) bval (apply-env saved-env search-sym)))
      (extend-env-recursively (id bvar body saved-env)
                              (if (eqv? search-sym id)
                                  (proc-val (procedure bvar body env))
                                  (apply-env saved-env search-sym)))
      (extend-env-with-module (m-name m-val saved-env)
                              (apply-env saved-env search-sym)))))

;; lookup-module-name-in-env : Sym * Env -> Typed-Module
(define lookup-module-name-in-env
  (lambda (m-name env)
    (cases
        environment
      env
      (empty-env
       ()
       (eopl:error 'lookup-module-name-in-env "No module binding for ~s" m-name))
      (extend-env (bvar bval saved-env)
                  (lookup-module-name-in-env m-name saved-env))
      (extend-env-recursively (id bvar body saved-env)
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
      (cases typed-module
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
(define-datatype
  type-environment
  type-environment?
  (empty-tenv)
  (extend-tenv (bvar symbol?) (bval type?) (saved-tenv type-environment?))
  (extend-tenv-with-module (name symbol?)
                           (interface interface?)
                           (saved-tenv type-environment?))
  (extend-tenv-with-type
   (name identifier?)
   (type type?)
   (saved-tenv type-environment?)))


;; lookup-qualified-var-in-tenv : Sym * Sym * Tenv -> Type
(define lookup-qualified-var-in-tenv
  (lambda (m-name var-name tenv)
    (let ([iface (lookup-module-name-in-tenv tenv m-name)])
      (cases interface
        iface
        (simple-iface (decls)
                      (lookup-variable-name-in-decls var-name decls))))))

(define lookup-type-name-in-tenv
  (lambda (tenv search-sym)
    (let ((maybe-answer
           (type-name->maybe-binding-in-tenv tenv search-sym)))
      (if maybe-answer maybe-answer
          (raise-tenv-lookup-failure-error 'type search-sym tenv)))))

;; type-name->maybe-binding-in-tenv : Tenv * Sym -> Maybe(ExpandedType)
(define type-name->maybe-binding-in-tenv
  (lambda (tenv search-sym)
    (let recur ((tenv tenv))
      (cases type-environment tenv
        (empty-tenv () #f)
        (extend-tenv-with-type (name type saved-tenv)
                               (if (eqv? name search-sym)
                                   type
                                   (recur saved-tenv)))
        (else (recur (tenv->saved-tenv tenv)))))))

(define lookup-qualified-type-in-tenv
  (lambda (m-name t-name tenv)
    (let ((iface (lookup-module-name-in-tenv tenv m-name)))
      (cases interface iface
        (simple-iface (decls)
                      ;; this is not right, because it doesn't distinguish
                      ;; between type and variable declarations.  Exercise: fix
                      ;; this so that it raises an error if t-name is declared
                      ;; in a val-decl.
                      (lookup-variable-name-in-decls t-name decls))
        ))))

(define lookup-variable-name-in-tenv
  (lambda (tenv search-sym)
    (let ([maybe-answer (variable-name->maybe-binding-in-tenv tenv search-sym)])
      (if maybe-answer
          maybe-answer
          (raise-tenv-lookup-failure-error 'variable search-sym tenv)))))

(define lookup-module-name-in-tenv
  (lambda (tenv search-sym)
    (let ([maybe-answer (module-name->maybe-binding-in-tenv tenv search-sym)])
      (if maybe-answer
          maybe-answer
          (raise-tenv-lookup-failure-error 'module search-sym tenv)))))

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
        [(null? decls) (raise-lookup-variable-in-decls-error! var-name decls0)]
        [(eqv? var-name (decl->name (car decls))) (decl->type (car decls))]
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
      (cases type-environment
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
    (cases type-environment tenv
      (empty-tenv ()
                  (eopl:error 'tenv->saved-tenv
                              "tenv->saved-tenv called on empty tenv"))
      (extend-tenv (name ty saved-tenv) saved-tenv)
      (extend-tenv-with-module (name m-type saved-tenv) saved-tenv)
      (extend-tenv-with-type (name ty saved-tenv) saved-tenv)
      )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Checker
; expand-type : Type × Tenv → ExpandedType
(define expand-type
  (lambda (ty tenv)
    (cases type ty
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (arg-type result-type)
                 (proc-type
                  (expand-type arg-type tenv)
                  (expand-type result-type tenv)))
      (named-type (name)
                  (lookup-type-name-in-tenv tenv name))
      (qualified-type (m-name t-name)
                      (lookup-qualified-type-in-tenv m-name t-name tenv)))))

;; expand-iface : Sym * Iface * Tenv -> Iface
(define expand-iface
  (lambda (m-name iface tenv)
    (cases interface iface
      (simple-iface (decls)
                    (simple-iface
                     (expand-decls m-name decls tenv))))))

;; expand-decls : Sym * Listof(Decl) * Tenv -> Listof(Decl)
(define expand-decls
  (lambda (m-name decls internal-tenv)
    (if (null? decls) '()
        (cases declaration (car decls)
          (opaque-type-decl (t-name)
                            ;; here the expanded type is m.t
                            (let ((expanded-type (qualified-type m-name t-name)))
                              (let ((new-env (extend-tenv-with-type
                                              t-name
                                              expanded-type
                                              internal-tenv)))
                                (cons
                                 (transparent-type-decl t-name expanded-type)
                                 (expand-decls m-name (cdr decls) new-env)))))
          (transparent-type-decl (t-name ty)
                                 (let ((expanded-type (expand-type ty internal-tenv)))
                                   (let ((new-env (extend-tenv-with-type
                                                   t-name
                                                   expanded-type
                                                   internal-tenv)))
                                     (cons
                                      (transparent-type-decl t-name expanded-type)
                                      (expand-decls m-name (cdr decls) new-env)))))
          (val-decl (var-name ty)
                    (let ((expanded-type
                           (expand-type ty internal-tenv)))
                      (cons
                       (val-decl var-name expanded-type)
                       (expand-decls m-name (cdr decls) internal-tenv))))))))

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
    (cases expression exp
      (const-exp (num) (int-type))

      (diff-exp (exp1 exp2)
                (let ((type1 (type-of exp1 tenv))
                      (type2 (type-of exp2 tenv)))
                  (check-equal-type! type1 (int-type) exp1)
                  (check-equal-type! type2 (int-type) exp2)
                  (int-type)))

      (zero?-exp (exp1)
                 (let ((type1 (type-of exp1 tenv)))
                   (check-equal-type! type1 (int-type) exp1)
                   (bool-type)))

      (if-exp (exp1 exp2 exp3)
              (let ((ty1 (type-of exp1 tenv))
                    (ty2 (type-of exp2 tenv))
                    (ty3 (type-of exp3 tenv)))
                (check-equal-type! ty1 (bool-type) exp1)
                (check-equal-type! ty2 ty3 exp)
                ty2))

      (var-exp (var) (apply-tenv tenv var))

      ;; lookup-qualified-var-in-tenv defined on page 285.
      (qualified-var-exp (m-name var-name)
                         (lookup-qualified-var-in-tenv m-name var-name tenv))

      (let-exp (var exp1 body)
               (let ((rhs-type (type-of exp1 tenv)))
                 (type-of body (extend-tenv var rhs-type tenv))))

      (proc-exp (bvar bvar-type body)
                (let ((expanded-bvar-type
                       (expand-type bvar-type tenv)))
                  (let ((result-type
                         (type-of body
                                  (extend-tenv
                                   bvar
                                   expanded-bvar-type
                                   tenv))))
                    (proc-type expanded-bvar-type result-type))))

      (call-exp (rator rand)
                (let ((rator-type (type-of rator tenv))
                      (rand-type  (type-of rand tenv)))
                  (cases type rator-type
                    (proc-type (arg-type result-type)
                               (begin
                                 (check-equal-type! arg-type rand-type rand)
                                 result-type))
                    (else
                     (eopl:error 'type-of
                                 "Rator not a proc type:~%~s~%had rator type ~s"
                                 rator (type-to-external-form rator-type))))))

      (letrec-exp (proc-result-type proc-name
                                    bvar bvar-type
                                    proc-body
                                    letrec-body)
                  (let ((tenv-for-letrec-body
                         (extend-tenv
                          proc-name
                          (expand-type
                           (proc-type bvar-type proc-result-type)
                           tenv)
                          tenv)))
                    (let ((proc-result-type
                           (expand-type proc-result-type tenv))
                          (proc-body-type
                           (type-of proc-body
                                    (extend-tenv
                                     bvar
                                     (expand-type bvar-type tenv)
                                     tenv-for-letrec-body))))
                      (check-equal-type!
                       proc-body-type proc-result-type proc-body)
                      (type-of letrec-body tenv-for-letrec-body))))

      )))

(define init-tenv
  (lambda ()
    (extend-tenv 'true
                 (bool-type)
                 (extend-tenv 'false (bool-type) (empty-tenv)))))

;; type-of-program : Program -> Type
(define type-of-program
  (lambda (pgm)
    (cases program
      pgm
      (a-program (module-defs body)
                 (let ([tenv (add-module-defns-to-tenv module-defs
                                                       (init-tenv))])
                   ; (eopl:pretty-print tenv)
                   (type-of body tenv))))))

;; add-module-defns-to-tenv : Listof(ModuleDefn) * Tenv -> Tenv
(define add-module-defns-to-tenv
  (lambda (defns tenv)
    (if (null? defns)
        tenv
        (cases module-definition (car defns)
          (a-module-definition (m-name expected-iface m-body)
                               (let ((actual-iface (interface-of m-body tenv)))
                                ;  (display "actual-iface:\n")
                                ;  (eopl:pretty-print actual-iface)
                                ;  (newline)
                                ;  (display "expected-iface:\n")
                                ;  (eopl:pretty-print expected-iface)
                                 ;  (newline)
                                 ;  (display "expand expected-iface:\n")
                                 ;  (eopl:pretty-print  (expand-iface m-name expected-iface tenv))
                                 ;;; why not
                                 ;  (<:-iface actual-iface (expand-iface m-name expected-iface tenv) tenv)
                                 (if (<:-iface actual-iface expected-iface tenv)
                                     ;; ok, continue in extended tenv
                                     (let ((new-env (extend-tenv-with-module
                                                     m-name
                                                     (expand-iface m-name expected-iface tenv)
                                                     tenv)))
                                       (add-module-defns-to-tenv (cdr defns) new-env))
                                     ;; no, raise error
                                     (report-module-doesnt-satisfy-iface m-name
                                                                         expected-iface actual-iface))))))))

;; interface-of : ModuleBody * Tenv -> Iface
(define interface-of
  (lambda (m-body tenv)
    (cases module-body
      m-body
      (defns-module-body (defns)
        (simple-iface (defns-to-decls defns tenv))))))

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
        (cases definition (car defns)
          (val-defn (var-name exp)
                    (let ((ty (type-of exp tenv)))
                      (let ((new-env (extend-tenv var-name ty tenv)))
                        (cons
                         (val-decl var-name ty)
                         (defns-to-decls (cdr defns) new-env)))))
          (type-defn (name ty)
                     ;;; code from book
                     ;  (let ((new-env (extend-tenv-with-type
                     ;                  name
                     ;                  (expand-type ty tenv)
                     ;                  tenv)))
                     ;    (cons
                     ;     (transparent-type-decl name ty)
                     ;     (defns-to-decls (cdr defns) new-env))))))))
                     ;;; I changed a little
                     (let ([ty (expand-type ty tenv)])
                       (let ((new-env (extend-tenv-with-type
                                       name
                                       ty
                                       tenv)))
                         (cons
                          (transparent-type-decl name ty)
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
         (simple-iface (decls2) (<:-decls decls1 decls2 tenv)))))))

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
    ; (display "______________________________________________________________________________\n")
    ; (display "decls1:\n")
    ; (eopl:pretty-print decls1)
    ; (newline)
    ; (display "decls2:\n")
    ; (eopl:pretty-print decls2)
    ; (display "______________________________________________________________________________\n")
    (cond
      ;; if nothing in decls2, any decls1 will do
      ((null? decls2) #t)
      ;; nothing in decls1 to match, so false
      ((null? decls1) #f)
      (else
       ;; at this point we know both decls1 and decls2 are non-empty.
       (let ((name1 (decl->name (car decls1)))
             (name2 (decl->name (car decls2))))
         (if (eqv? name1 name2)
             ;; same name.  They'd better match
             (and
              (<:-decl (car decls1) (car decls2) tenv)
              (<:-decls (cdr decls1) (cdr decls2)
                        (extend-tenv-with-decl (car decls1) tenv)))
             ;; different names.  OK to skip, but record decl1 in the tenv.
             (<:-decls (cdr decls1) decls2
                       (extend-tenv-with-decl (car decls1) tenv))))))))

;; extend-tenv-with-decl : Decl * Tenv -> Tenv
(define extend-tenv-with-decl
  (lambda (decl tenv)
    (cases declaration decl
      ;; don't need to record val declarations
      (val-decl (name ty) tenv)
      (transparent-type-decl (name ty)
                             (extend-tenv-with-type
                              name
                              (expand-type ty tenv)
                              tenv))
      (opaque-type-decl (name)
                        (extend-tenv-with-type
                         name
                         ;; the module name doesn't matter, since the only
                         ;; operation on qualified types is equal?
                         (qualified-type (fresh-module-name '%abstype) name)
                         tenv)))))

;; decl1 and decl2 are known to declare the same name.  There are
;; exactly four combinations that can succeed.

;; <:-decl : Decl * Decl * Tenv -> Bool
(define <:-decl
  (lambda (decl1 decl2 tenv)
    (or
     (and
      (val-decl? decl1)
      (val-decl? decl2)
      (equiv-type? (decl->type decl1) (decl->type decl2) tenv))
     (and
      (transparent-type-decl? decl1)
      (transparent-type-decl? decl2)
      (equiv-type? (decl->type decl1) (decl->type decl2) tenv))
     (and
      (transparent-type-decl? decl1)
      (opaque-type-decl? decl2))
    ;  (and
    ;   (opaque-type-decl? decl1) ; how could decls be opaque-type-decl? decl1 is built from defns-to-decls
    ;   (opaque-type-decl? decl2))
     )))

;; equiv-type? : Type * Type * Tenv -> Bool
(define equiv-type?
  (lambda (ty1 ty2 tenv)
    (equal?
     (expand-type ty1 tenv)
     (expand-type ty2 tenv))))

(define rename-in-iface
  (lambda (m-type old new)
    (cases interface m-type
      (simple-iface (decls)
                    (simple-iface
                     (rename-in-decls decls old new))) )))

;; this isn't a map because we have let* scoping in a list of declarations
(define rename-in-decls
  (lambda (decls old new)
    (if (null? decls) '()
        (let ((decl (car decls))
              (decls (cdr decls)))
          (cases declaration decl
            (val-decl (name ty)
                      (cons
                       (val-decl name (rename-in-type ty old new))
                       (rename-in-decls decls old new)))
            (opaque-type-decl (name)
                              (cons
                               (opaque-type-decl name)
                               (if (eqv? name old)
                                   decls
                                   (rename-in-decls decls old new))))
            (transparent-type-decl (name ty)
                                   (cons
                                    (transparent-type-decl
                                     name
                                     (rename-in-type ty old new))
                                    (if (eqv? name old)
                                        decls
                                        (rename-in-decls decls old new))))
            )))))

(define rename-in-type
  (lambda (ty old new)
    (let recur ((ty ty))
      (cases type ty
        (named-type (id)
                    (named-type (rename-name id old new)))
        (qualified-type (m-name name)
                        (qualified-type
                         (rename-name m-name old new)
                         name))
        (proc-type (t1 t2)
                   (proc-type (recur t1) (recur t2)))
        (else ty)              ; this covers int, bool, and unknown.
        ))))

(define rename-name
  (lambda (name old new)
    (if (eqv? name old) new name)))

(define fresh-module-name
  (let ((sn 0))
    (lambda (module-name)
      (set! sn (+ sn 1))
      (string->symbol
       (string-append
        (symbol->string module-name)
        "%"             ; this can't appear in an input identifier
        (number->string sn))))))

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
       (let ([env (add-module-defns-to-env module-defs (init-env))])
         ; (eopl:pretty-print env)
         (value-of body env))))))

;; add-module-defns-to-env : Listof(Defn) * Env -> Env
(define add-module-defns-to-env
  (lambda (defs env)
    (if (null? defs)
        env
        (cases module-definition
          (car defs)
          (a-module-definition (m-name iface m-body)
                               (add-module-defns-to-env
                                (cdr defs)
                                (extend-env-with-module
                                 m-name
                                 (value-of-module-body m-body env)
                                 env)))))))

;; value-of-module-body : ModuleBody * Env -> TypedModule
(define value-of-module-body
  (lambda (m-body env)
    (cases module-body
      m-body
      (defns-module-body (defns)
        (simple-module (defns-to-env defns env))))))

(define raise-cant-apply-non-proc-module!
  (lambda (rator-val)
    (eopl:error 'value-of-module-body
                "can't apply non-proc-module-value ~s"
                rator-val)))

;; defns-to-env : Listof(Defn) * Env -> Env
(define defns-to-env
  (lambda (defns env)
    (if (null? defns)
        (empty-env)
        (cases definition (car defns)
          (val-defn
           (var exp)
           (let ([val (value-of exp env)])
             ;; new environment for subsequent definitions
             (let ([new-env (extend-env var val env)])
               (extend-env var val (defns-to-env (cdr defns) new-env)))))
          (type-defn (type-name type)
                     (defns-to-env (cdr defns) env))))))

;; value-of : Exp * Env -> ExpVal
(define value-of
  (lambda (exp env)

    (cases expression
      exp
      (const-exp (num) (num-val num))
      (var-exp (var) (apply-env env var))
      (qualified-var-exp (m-name var-name)
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
       (value-of letrec-body
                 (extend-env-recursively proc-name bvar proc-body env))))))

;; apply-procedure : Proc * ExpVal -> ExpVal
(define apply-procedure
  (lambda (proc1 arg)
    (cases proc
      proc1
      (procedure (var body saved-env)
                 (value-of body (extend-env var arg saved-env))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; test
(define :e (lambda (str) (value-of-program (scan&parse str))))
(define :t (lambda (str) (type-to-external-form (type-of-program (scan&parse str)))))

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
  "module ints
    interface
      [opaque t
       zero : t
       succ : (t -> t)
       pred : (t -> t)
       is-zero : (t -> bool)]
    body
       [type t = int
       zero = 3
       succ = proc(x : t) -(x, -5)
       pred = proc(x : t) -(x, 5)
       is-zero = proc (x : t) zero?(-(x, 3))]
    let z = from ints take zero
    in let s = from ints take succ
    in let p = from ints take pred
    in let z? = from ints take is-zero
    in letrec int to-int (x : from ints take t) =
                    if (z? x)
                    then 0
                    else -((to-int (p x)), -1)
    in (to-int (s (s z)))
  ")
(check-equal? (:e str5) (num-val 2))
(check-equal? (:t str5) 'int)

(define str6
  "
module tables
  interface
    [opaque table
    empty : table
    add-to-table : (int -> (int -> (table -> table)))
    lookup-in-table : (int -> (table -> int))]
  body
    [type table = (int -> int)
     empty = proc(x: int) -1
     add-to-table = proc(x: int)
                      proc(y: int)
                        proc(saved: table)
                          proc(search: int)
                            if zero?(-(x, search))
                            then y
                            else (saved search)
     lookup-in-table = proc(search: int)
                         proc(t: table)
                           (t search)
    ]
let empty = from tables take empty
in let add-binding = from tables take add-to-table
in let lookup = from tables take lookup-in-table
in let table1 = (((add-binding 3) 300)
                 (((add-binding 4) 400)
                  (((add-binding 3) 600)
                   empty)))
in -(((lookup 4) table1),
((lookup 3) table1))
  ")
(check-equal? (:e str6) (num-val 100))
(check-equal? (:t str6) 'int)

(define str7
  "module m1
     interface
       [opaque t
       z : t
       s : (t -> t)
       is-z? : (t -> bool)]
     body
       [type t = int
       z = 33
       s = proc (x : t) -(x,-1)
       is-z? = proc (x : t) zero?(-(x,z))]
    proc (x : from m1 take t)
      (from m1 take is-z? x)")
(check-true (proc? (expval->proc (:e str7))))
(check-equal? (:t str7) '((from m1 take t) -> bool))

(define str8
  "module colors
     interface
       [opaque color
       red : color
       green : color
       is-red? : (color -> bool)]
     body
       [type color = int
       red = 0
       green = 1
       is-red? = proc (c : color) zero?(c)]
   let c = from colors take green
   in let f = from colors take is-red?
   in (f c)")
(check-equal? (:e str8) (bool-val #f))
(check-equal? (:t str8) 'bool)

(define str9
  "module ints1
     interface
       [opaque t
       zero : t
       succ : (t -> t)
       pred : (t -> t)
       is-zero : (t -> bool)]
     body
       [type t = int
       zero = 0
       succ = proc(x : t) -(x,-5)
       pred = proc(x : t) -(x,5)
       is-zero = proc (x : t) zero?(x)]
   let z = from ints1 take zero
   in let s = from ints1 take succ
      in (s (s z))")
(check-equal? (:e str9) (num-val 10))
(check-equal? (:t str9) '(from ints1 take t))

(define str10
  "module mybool
     interface
       [opaque t
       true : t
       false : t
       and : (t -> (t -> t))
       not : (t -> t)
       to-bool : (t -> bool)]
     body
       [type t = int
       true = 0
       false = 13
       and = proc (x : t)
               proc (y : t)
               if zero?(x) then y else false
       not = proc (x : t)
               if zero?(x) then false else true
       to-bool = proc (x : t) zero?(x)]
     let true = from mybool take true
     in let false = from mybool take false
        in let and = from mybool take and
           in ((and true) false)")
(check-equal? (:e str10) (num-val 13))
(check-equal? (:t str10) '(from mybool take t))

(define str11
  "module m1
     interface
       [opaque i
        transparent ib = (i -> bool)
        x: i
        f: ib
        ]
     body
       [type i = int
        %type ib = (int -> bool) %ok
        type ib = (i -> bool) %ok
        %type ib = (from m1 take i -> bool) %not ok
        x = 0
        f = proc(v: int) zero?(v)]
    from m1 take f
  ")
(check-equal? (:t str11) '((from m1 take i) -> bool))
(check-true (proc? (expval->proc (:e str11))))

(define str12
  "module m1
   interface
     [opaque t
      transparent u = (t -> int)
      f : (t -> (int -> int))]
   body
     [type t = int
      type u = (t -> t)
      f = proc(x: t) proc(y: t) y]
   13")
(check-equal? (:t str12) 'int)

(define str13
  "module m1
   interface
     [opaque t
      transparent u = (t -> t)]
   body
     [type t = int
      type u = (t -> t)]
   13")
(check-equal? (:t str13) 'int)
