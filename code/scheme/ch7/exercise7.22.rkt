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
; (define apply-one-subst
;   (lambda (ty0 tvar ty1)
;     (cases type ty0
;       (int-type () (int-type))
;       (bool-type () (bool-type))
;       (proc-type (arg-type result-type)
;                  (proc-type
;                   (apply-one-subst arg-type tvar ty1)
;                   (apply-one-subst result-type tvar ty1)))
;       (tvar-type (sn)
;                  (if (equal? ty0 tvar) ty1 ty0)))))

; apply-subst-to-type : Type × Subst → Type
(define apply-subst-to-type
  (lambda (ty)
    (cases type ty
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (t1 t2)
                 (proc-type
                  (apply-subst-to-type t1)
                  (apply-subst-to-type t2)))
      (tvar-type (sn)
                 (let ((tmp (the-subst-ref ty)))
                   (if tmp
                       (apply-subst-to-type tmp)
                       ty))))))

; empty-subst : () → Subst
(define empty-subst (lambda () (make-vector 128 #f)))

; extend-subst : Subst × Tvar × Type → Subst
(define extend-subst
  (lambda (tvar ty)
    (cases type tvar
      [tvar-type (serial-number)
                 (let ([old-len (vector-length the-subst)])
                   (if (>= serial-number old-len)
                       (let ((new-subst (make-vector (* 2 old-len))))
                         (let copy ([i 0])
                           (if (= i old-len)
                               (begin (vector-set! new-subst i ty)
                                      (set! the-subst new-subst))
                               (begin (vector-set! new-subst i (vector-ref the-subst i))
                                      (copy (+ 1 i))))))
                       (vector-set! the-subst serial-number ty)))]
      [else (eopl:error 'extend-subst "Not a variable type: ~s" ty)])))

(define the-subst-ref
  (lambda (ty)
    (cases type ty
      [tvar-type (serial-number) (vector-ref the-subst serial-number)]
      [else (eopl:error 'subst-ref "Not a variable type: ~s" ty)])))

(define the-subst
  'uninitialized)

(define initialize-subst!
  (lambda ()
    (set! the-subst (empty-subst))))

(initialize-subst!)

; unifier : Type × Type × Subst × Exp → '()
(define unifier
  (lambda (ty1 ty2 exp)
    (let ((ty1 (apply-subst-to-type ty1))
          (ty2 (apply-subst-to-type ty2)))
      (cond
        ((equal? ty1 ty2) '())
        ((tvar-type? ty1)
         (if (no-occurrence? ty1 ty2)
             (extend-subst ty1 ty2)
             (report-no-occurrence-violation ty1 ty2 exp)))
        ((tvar-type? ty2)
         (if (no-occurrence? ty2 ty1)
             (extend-subst ty2 ty1)
             (report-no-occurrence-violation ty2 ty1 exp)))
        ((and (proc-type? ty1) (proc-type? ty2))
         (unifier
          (proc-type->arg-type ty1)
          (proc-type->arg-type ty2)
          exp)
         (unifier
          (proc-type->result-type ty1)
          (proc-type->result-type ty2)
          exp))
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