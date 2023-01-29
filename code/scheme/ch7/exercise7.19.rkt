#lang eopl
#|
The no-occurrence invariant: 
No variable bound in the substitution occurs in any of the right-hand sides of the substitution.

(define apply-subst-to-type
   ...
   (tvar-type (sn)
                 (let ((tmp (assoc ty subst)))
                   (if tmp
                       (cdr tmp) ;  in the right-hand sides, according to the no-occurrence invariant, it is unbound
                       ty))))))  ;  unbound
|#