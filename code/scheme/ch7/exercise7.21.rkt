#lang eopl

(define-datatype
  type
  type?
  (int-type)
  (bool-type)
  (proc-type (arg-type type?) (result-type type?))
  (tvar-type (num number?)))

(define proc-type?
  (lambda (ty)
    (cases type ty
      [proc-type (t1 t2) #t]
      [else #f])))

(define tvar-type?
  (lambda (ty)
    (cases type ty
      [tvar-type (serial-number) #t]
      [else #f])))

(define proc-type->arg-type
  (lambda (ty)
    (cases type ty
      [proc-type (arg-type result-type) arg-type]
      [else (eopl:error 'proc-type->arg-type "Not a proc type: ~s" ty)])))

(define proc-type->result-type
  (lambda (ty)
    (cases type ty
      [proc-type (arg-type result-type) result-type]
      [else (eopl:error 'proc-type->result-types "Not a proc type: ~s" ty)])))


(define type-to-external-form
  (lambda (ty)
    (cases type ty
      (int-type () 'int)
      (bool-type () 'bool)
      (proc-type (arg-type result-type) (list (type-to-external-form arg-type) '-> (type-to-external-form result-type)))
      (tvar-type (serial-number) (string->symbol (string-append "tvar" (number->string serial-number)))))))

; apply-one-subst : Type × Tvar × Type → Type
(define apply-one-subst
  (lambda (ty0 tvar ty1)
    (cases type ty0
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (arg-type result-type)
                 (proc-type
                  (apply-one-subst arg-type tvar ty1)
                  (apply-one-subst result-type tvar ty1)))
      (tvar-type (sn)
                 (if (equal? ty0 tvar) ty1 ty0)))))

; apply-subst-to-type : Type × Subst → Type
(define apply-subst-to-type
  (lambda (ty subst)
    (cases type ty
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (t1 t2)
                 (proc-type
                  (apply-subst-to-type t1 subst)
                  (apply-subst-to-type t2 subst)))
      (tvar-type (sn)
                 (let ((tmp (assoc ty subst)))
                   (if tmp
                       (remove-tvars (cdr tmp) subst)
                       ty))))))

; remove-tvars : Type × Subst → Type
(define remove-tvars
  (lambda (ty subst)
    (cases type ty
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (t1 t2)
                 (proc-type (remove-tvars t1 subst)
                            (remove-tvars t2 subst)))
      (tvar-type (sn)
                 (let ((p (assoc ty subst)))
                   (if p
                       (remove-tvars (cdr p) subst)
                       (eopl:error 'remove-tvars)))))))

; empty-subst : () → Subst
(define empty-subst (lambda () '()))

; extend-subst : Subst × Tvar × Type → Subst
(define extend-subst
  (lambda (subst tvar ty)
    (cons (cons tvar ty) subst)))

(define the-subst
  'uninitialized)

(define initialize-subst!
  (lambda ()
    (set! the-subst (empty-subst))))

(initialize-subst!)

; unifier : Type × Type × Subst × Exp → '()
(define unifier
  (lambda (ty1 ty2 exp)
    (let ((ty1 (apply-subst-to-type ty1 the-subst))
          (ty2 (apply-subst-to-type ty2 the-subst)))
      (cond
        ((equal? ty1 ty2) '())
        ((tvar-type? ty1)
         (if (no-occurrence? ty1 ty2)
             (begin (set! the-subst (extend-subst the-subst ty1 ty2))
                    '())
             (report-no-occurrence-violation ty1 ty2 exp)))
        ((tvar-type? ty2)
         (if (no-occurrence? ty2 ty1)
             (begin (set! the-subst (extend-subst the-subst ty2 ty1))
                    '())
             (report-no-occurrence-violation ty2 ty1 exp)))
        ((and (proc-type? ty1) (proc-type? ty2))
         (begin (unifier
                 (proc-type->arg-type ty1)
                 (proc-type->arg-type ty2)
                 exp)
                (unifier
                 (proc-type->result-type ty1)
                 (proc-type->result-type ty2)
                 exp)
                '()))
        (else (report-unification-failure ty1 ty2 exp))))))

; no-occurrence? : Tvar × Type → Bool
(define no-occurrence?
  (lambda (tvar ty)
    (cases type ty
      (int-type () #t)
      (bool-type () #t)
      (proc-type (arg-type result-type)
                 (and
                  (no-occurrence? tvar arg-type)
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
    (eopl:error 'check-no-occurence!
                "Can't unify: type variable ~s occurs in type ~s in expression ~s~%"
                (type-to-external-form ty1)
                (type-to-external-form ty2)
                exp)))

;;; test
'todo