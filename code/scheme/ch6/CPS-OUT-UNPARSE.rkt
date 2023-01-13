#lang eopl
(require racket/format)
(require racket/string)
(require rackunit)
(require "CPS-OUT.rkt")
(require "CPS-TRANSFORM.rkt")
(define unparse-simple
  (lambda (simple)
    (cases
        simple-expression
      simple
      (cps-const-exp (num) (~a num))
      (cps-var-exp (var) (~a var))
      (cps-diff-exp (exp1 exp2)
                    (~a "-" "(" (unparse-simple exp1) ", " (unparse-simple exp2) ")"))
      (cps-sum-exp
       (exps)
       (let ([unparsed (map unparse-simple exps)])
         (if (null? unparsed)
             "+()"
             (let loop ([rest (cdr unparsed)]
                        [res (~a "+(" (car unparsed))])
               (if (null? rest)
                   (~a res ")")
                   (loop (cdr rest) (~a res ", " (car rest))))))))
      (cps-zero?-exp (exp1)
                     (~a "zero?" "(" (unparse-simple exp1) ")"))
      (cps-proc-exp (vars body) (~a "proc" (~a vars) " " (unparse-tf body))))))

(define unparse-tf
  (lambda (exp)
    (cases
        tfexp
      exp
      (simple-exp->exp (simple)
                       (unparse-simple simple))
      (cps-let-exp (var rhs body)
                   (~a "let" " " var " = " (unparse-simple rhs) " in " (unparse-tf body) " "))
      (cps-letrec-exp (p-names b-varss p-bodies letrec-body)
                      (let ((unparsed-procs (map
                                             (lambda (p-name b-vars p-body)
                                               (~a p-name b-vars " = " (unparse-tf p-body)))
                                             p-names b-varss p-bodies)))
                        (let loop ([unparsed-procs unparsed-procs]
                                   [res "letrec "])
                          (if (null? unparsed-procs)
                              (~a res " in " (unparse-tf letrec-body) " ")
                              (loop (cdr unparsed-procs) (~a res (car unparsed-procs) "\n"))))))


      (cps-if-exp (simple1 body1 body2)
                  (~a " if " (unparse-simple simple1)
                      " then " (unparse-tf body1)
                      " else " (unparse-tf body2)))
      (cps-call-exp
       (rator rands)
       (let ([unparsed-rator (unparse-simple rator)]
             [unparsed-rands (map unparse-simple rands)])
         (let loop ([unparsed-rands unparsed-rands]
                    [res (~a "(" unparsed-rator)])
           (if (null? unparsed-rands)
               (~a res ")")
               (loop (cdr unparsed-rands) (~a res " " (car unparsed-rands))))))))))

(define unparse
  (lambda (pgm)
    (cases cps-out-program
      pgm
      (cps-a-program (exp1)
                     (let ((unparsed (unparse-tf exp1)))
                       (string-replace unparsed "%" "")))))) ; remove %, because it's the comment start symbol
                              

;;; test
(define str0
  "
  letrec double(x k)
          = if zero?(x) then (k 0) else (double -(x, 1) proc(v0) (k -(v0, -2)))
  in (double 7 proc(x) +(x, 1))
   ")
(check-equal? (run (unparse (scan&parse str0))) (num-val 15))

(define str1
  "letrec equal?(x n) = if zero?(x)
                             then zero?(n)
                             else (equal? -(x, 1) -(n, 1))
   in let f = proc(x) x
      in let g = proc(x y) +(x, y, 37)
         in let h = proc(x y z) +(x, y, z, 17)
            in let y = 73
               in let p = proc(x) if zero?(x)
                                  then 17
                                  else if (equal? x 1)
                                       then (f -(x, 13))
                                       else if (equal? x 2)
                                            then +(22, -(x, 3), x)
                                            else if (equal? x 3)
                                                 then +(22, (f x), 37)
                                                 else if (equal? x 4)
                                                      then (g 22 (f x))
                                                      else if (equal? x 5)
                                                           then +(22, (f x), 33, (g y 37))
                                                           else (h (f x) -(44, y) (g y 37))
                   in +((p 1), (p 2), (p 3), (p 4), (p 5), (p 73))")
(check-equal? (run (unparse (transform str1))) (num-val 551))

(define str2
  "let f = proc(x) x
   in (f 73)")
#|
let id = rhs in body
=> (proc(id) body rhs)

let f = proc(x) x in (f 73)
=> (proc(f) (f 73) proc(x) x)
=> (proc(f k) (f 73 k) proc(x k) (k x) proc(x) x)

let f = proc(x k) (k x)
in (f 73 proc(x) x)
|#
(check-equal? (run (unparse (transform str2))) (num-val 73))

(define str3
  "proc(f) proc(x) (f x)
  ")
(unparse (transform str3))

(define str4
  "proc(x) x
  ")
(unparse (transform str4))

(define str5
  "proc(x) if zero?(x)
           then 17
           else if (equal? x 1)
                then (f -(x, 13))
                else if (equal? x 2)
                     then +(22, -(x, 3), x)
                     else if (equal? x 3)
                          then +(22, (f x), 37)
                          else if (equal? x 4)
                               then (g 22 (f x))
                               else if (equal? x 5)
                                    then +(22, (f x), 33, (g y 37))
                                    else (h (f x) -(44, y) (g y 37))
  ")
(unparse (transform str5))
