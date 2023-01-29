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

; remove-tvars : Type × Subst → Type × Subst
(define remove-tvars
  (lambda (ty subst cache)
    (cases type ty
      (int-type () (list (int-type) cache))
      (bool-type () (list (bool-type) cache))
      (proc-type (t1 t2)
                 (let ((res1 (remove-tvars t1 subst cache)))
                   (let ((res-t1 (car res1))
                         (res-cache1 (cadr res1)))
                     (let ((res2
                            (remove-tvars t2 subst
                                          (cons (cons t1 res-t1) res-cache1))))
                       (let ((res-t2 (car res2))
                             (res-cache2 (cadr res2)))
                         (list (proc-type res-t1 res-t2)
                               (cons (cons t2 res-t2) res-cache2)))))))
      (tvar-type (sn)
                 (let ((from-cache (assoc ty cache)))
                   (if from-cache
                       (list (cdr from-cache) cache)
                       (let ((p (assoc ty subst)))
                         (if p
                             (remove-tvars (cdr p) subst cache)
                             (eopl:error 'remove-tvars)))))))))

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
                       (car (remove-tvars (cdr tmp) subst '()))
                       ty))))))

; empty-subst : () → Subst
(define empty-subst (lambda () '()))

; extend-subst : Subst × Tvar × Type → Subst
(define extend-subst
  (lambda (subst tvar ty)
    (cons (cons tvar ty) subst)))


;;; test
'todo
