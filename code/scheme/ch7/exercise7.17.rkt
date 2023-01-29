#lang eopl

(define-datatype
  type
  type?
  (int-type)
  (bool-type)
  (proc-type (arg-type type?) (result-type type?))
  (tvar-type (num number?)))

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
; (define apply-subst-to-type
;   (lambda (ty subst)
;     (cases type ty
;       (int-type () (int-type))
;       (bool-type () (bool-type))
;       (proc-type (t1 t2)
;                  (proc-type
;                   (apply-subst-to-type t1 subst)
;                   (apply-subst-to-type t2 subst)))
;       (tvar-type (sn)
;                  (let ((tmp (assoc ty subst)))
;                    (if tmp
;                        (cdr tmp)
;                        ty))))))
                     
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
; usage: tvar not already bound in subst.
; (define extend-subst
;   (lambda (subst tvar ty)
;     (cons
;      (cons tvar ty)
;      (map
;       (lambda (p)
;         (let ((oldlhs (car p))
;               (oldrhs (cdr p)))
;           (cons
;            oldlhs
;            (apply-one-subst oldrhs tvar ty))))
;       subst))))

(define extend-subst
  (lambda (subst tvar ty)
    (cons (cons tvar ty) subst)))

; For this definition of extend-subst, is the no-occurrence invariant needed?
; No need

;;; test
'todo