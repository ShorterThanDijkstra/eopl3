#lang eopl
(require "CPS-OUT-EFFECTS.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Expression data type
(require rackunit)
(define cps-in-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define cps-in-grammar-spec
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression (identifier) var-exp) ; deref
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("+" "(" (separated-list expression ",") ")") sum-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp) ; newref
    (expression
     ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" expression)
               "in"
               expression) ; newref
     letrec-exp)
    (expression ("proc" "(" (arbno identifier) ")" expression) proc-exp)
    (expression ("print" "(" expression ")") print-exp)
    (expression ("set" identifier "=" expression) assign-exp) ; setref
    (expression ("(" expression (arbno expression) ")") call-exp) ; newref
    ))

(define scan&parse-cps-in
  (sllgen:make-string-parser cps-in-lexical-spec cps-in-grammar-spec))

(sllgen:make-define-datatypes cps-in-lexical-spec cps-in-grammar-spec)

(define list-the-datatypes
  (lambda ()
    (sllgen:list-define-datatypes cps-in-lexical-spec cps-in-grammar-spec)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Helper Functions
(define list-set
  (lambda (lst n val)
    (cond
      [(null? lst) (eopl:error 'list-set "ran off end")]
      [(zero? n) (cons val (cdr lst))]
      [else (cons (car lst) (list-set (cdr lst) (- n 1) val))])))

(define list-index
  (lambda (pred lst)
    (cond
      [(null? lst) #f]
      [(pred (car lst)) 0]
      [(list-index pred (cdr lst))
       =>
       (lambda (n) (+ n 1))]
      [else #f])))

(define every?
  (lambda (pred lst)
    (cond
      [(null? lst) #t]
      [(pred (car lst)) (every? pred (cdr lst))]
      [else #f])))

(define identifier? (lambda (exp) (and (symbol? exp) (not (eqv? exp 'lambda)))))

(define fresh-identifier
  (let ([sn 0])
    (lambda (identifier)
      (set! sn (+ sn 1))
      (string->symbol
       (string-append (symbol->string identifier)
                      "%" ; this can't appear in an input identifier
                      (number->string sn))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Converter

; make-send-to-cont : SimpleExp × SimpleExp → TfExp
(define make-send-to-cont
  (lambda (k-exp simple-exp) (cps-call-exp k-exp (list simple-exp))))

(define report-invalid-exp-to-cps-of-simple-exp
  (lambda (exp)
    (eopl:error 'cps-simple-of-exp
                "non-simple expression to cps-of-simple-exp: ~s"
                exp)))

; cps-of-exps : Listof(InpExp) × (Listof(InpExp) → TfExp) → TfExp
(define cps-of-exps
  (lambda (exps builder)
    (let cps-of-rest ((exps exps) (acc '()))
      ; cps-of-rest : Listof(InpExp) × Listof(SimpleExp) → TfExp
      (cond
        ((null? exps) (builder (reverse acc)))
        ((inp-exp-simple? (car exps))
         (cps-of-rest (cdr exps)
                      (cons
                       (cps-of-simple-exp (car exps))
                       acc)))
        (else
         (let ((var (fresh-identifier 'var)))
           (cps-of-exp (car exps)
                       (cps-proc-exp (list var)
                                     (cps-of-rest (cdr exps)
                                                  (cons
                                                   (cps-of-simple-exp (var-exp var))
                                                   acc))))))))))

; inp-exp-simple? : InpExp → Bool
(define inp-exp-simple?
  (lambda (exp)
    (cases
        expression
      exp
      (const-exp (num) #t)
      ; (var-exp (var) #t)
      (diff-exp (exp1 exp2) (and (inp-exp-simple? exp1) (inp-exp-simple? exp2)))
      (zero?-exp (exp1) (inp-exp-simple? exp1))
      (proc-exp (ids exp) #t)
      (sum-exp (exps) (every? inp-exp-simple? exps))
      (else #f))))

; cps-of-exp : InpExp × SimpleExp → TfExp
(define cps-of-exp
  (lambda (exp k-exp)
    (cases
        expression
      exp
      (const-exp (num) (make-send-to-cont k-exp (cps-const-exp num)))
      (var-exp (var) (cps-of-var-exp var k-exp))
      (proc-exp (vars body)
                (make-send-to-cont
                 k-exp
                 (cps-proc-exp (append vars (list 'k%00))
                               (cps-of-exp body (cps-var-exp 'k%00)))))
      (zero?-exp (exp1) (cps-of-zero?-exp exp1 k-exp))
      (diff-exp (exp1 exp2) (cps-of-diff-exp exp1 exp2 k-exp))
      (sum-exp (exps) (cps-of-sum-exp exps k-exp))
      (if-exp (exp1 exp2 exp3) (cps-of-if-exp exp1 exp2 exp3 k-exp))
      (let-exp (var exp1 body) (cps-of-let-exp var exp1 body k-exp))
      (letrec-exp (p-names b-varss p-bodies letrec-body)
                  (cps-of-letrec-exp p-names b-varss p-bodies letrec-body k-exp))
      (print-exp (rator)
                 (cps-of-print-exp rator k-exp))
      (assign-exp (var exp1) (cps-of-assign-exp var exp1 k-exp))
      (call-exp (rator rands) (cps-of-call-exp rator rands k-exp)))))

(define cps-of-var-exp
  (lambda (var k-exp)
    (cps-deref-exp (cps-var-exp var) k-exp)))

#|
set x = 17

setref(x, 17); k
|#
(define cps-of-assign-exp
  (lambda (var exp1 k-exp)
    (cps-of-exps (list exp1)
                 (lambda (simples)
                   (cps-setref-exp (cps-var-exp var)
                                   (car simples)
                                   (make-send-to-cont k-exp (cps-const-exp 23)))))))

(define cps-of-print-exp
  (lambda (rator k-exp)
    (cps-of-exps (list rator)
                 (lambda (simples)
                   (cps-print-exp
                    (car simples)
                    (make-send-to-cont k-exp (cps-const-exp 38)))))))

; cps-of-sum-exp : Listof(InpExp) × SimpleExp → TfExp
(define cps-of-sum-exp
  (lambda (exps k-exp)
    (cps-of-exps exps
                 (lambda (simples)
                   (make-send-to-cont k-exp (cps-sum-exp simples))))))

; cps-of-simple-exp : InpExp → SimpleExp
; usage: assumes (inp-exp-simple? exp).
(define cps-of-simple-exp
  (lambda (exp)
    (cases
        expression
      exp
      (const-exp (num) (cps-const-exp num))
      (var-exp (var) (cps-var-exp var))
      (diff-exp (exp1 exp2)
                (cps-diff-exp (cps-of-simple-exp exp1) (cps-of-simple-exp exp2)))
      (zero?-exp (exp1) (cps-zero?-exp (cps-of-simple-exp exp1)))
      (proc-exp (ids exp)
                (cps-proc-exp (append ids (list 'k%00))
                              (cps-of-exp exp (cps-var-exp 'k%00))))
      (sum-exp (exps) (cps-sum-exp (map cps-of-simple-exp exps)))
      (else (report-invalid-exp-to-cps-of-simple-exp exp)))))

; cps-of-call-exp : InpExp × Listof(InpExp) × SimpleExp → TfExp
; (define cps-of-call-exp
  ; (lambda (rator rands k-exp)
    ; (cps-of-exps (cons rator rands)
                ;  (lambda (simples)
                  ;  (cps-call-exp (car simples)
                                ;  (append (cdr simples) (list k-exp)))))))

;;; copied from https://github.com/EFanZh/EOPL-Exercises/blob/master/solutions/exercise-6.37.rkt
(define cps-of-call-exp
  (lambda (rator rands k-exp)
    (cps-of-exps (cons rator rands)
                 (lambda (simples)
                   (define rator-simple (car simples))
                   (let loop ([acc '()]
                              [rands (cdr simples)])
                     (if (null? rands)
                         (cps-call-exp rator-simple (reverse (cons k-exp acc)))
                         (let ([var (fresh-identifier 'var)])
                           (cps-newref-exp (car rands)
                                           (cps-proc-exp (list var)
                                                         (loop (cons (cps-var-exp var) acc)
                                                               (cdr rands)))))))))))


; cps-of-zero?-exp : InpExp × SimpleExp → TfExp
(define cps-of-zero?-exp
  (lambda (exp1 k-exp)
    (cps-of-exps (list exp1)
                 (lambda (simples)
                   (make-send-to-cont k-exp (cps-zero?-exp (car simples)))))))

; cps-of-diff-exp : InpExp × InpExp × SimpleExp → TfExp
(define cps-of-diff-exp
  (lambda (exp1 exp2 k-exp)
    (cps-of-exps
     (list exp1 exp2)
     (lambda (simples)
       (make-send-to-cont k-exp (cps-diff-exp (car simples) (cadr simples)))))))

; cps-of-if-exp : InpExp × InpExp × InpExp × SimpleExp → TfExp
(define cps-of-if-exp
  (lambda (exp1 exp2 exp3 k-exp)
    (cps-of-exps (list exp1)
                 (lambda (simples)
                   (cps-if-exp (car simples)
                               (cps-of-exp exp2 k-exp)
                               (cps-of-exp exp3 k-exp))))))

; cps-of-let-exp : Var × InpExp × InpExp × SimpleExp → TfExp
; (define cps-of-let-exp ;;; why this fails?
;   (lambda (id rhs body k-exp)
;     (cps-of-exps (list rhs)
;                  (lambda (simples)
;                    (cps-let-exp id
;                                 (car simples)
;                                 (cps-of-exp body k-exp))))))
; (define cps-of-let-exp
;   (lambda (id rhs body k-exp)
; (cps-of-exp (call-exp (proc-exp (list id) body) (list rhs)) k-exp)))
(define cps-of-let-exp
  (lambda (id rhs body k-exp)
    (cps-of-exps (list rhs)
                 (lambda (simples)
                   (cps-newref-exp  (car simples)
                                    (cps-proc-exp (list id)
                                                  (cps-of-exp body k-exp)))))))

; cps-of-letrec-exp :
; Listof(Listof(Var)) * Listof(InpExp) * InpExp * SimpleExp -> TfExp
; (define cps-of-letrec-exp
; (lambda (p-names b-varss p-bodies letrec-body k-exp)
; (cps-letrec-exp
;  p-names
;  (map (lambda (b-vars) (append b-vars (list 'k%00))) b-varss)
;  (map (lambda (p-body) (cps-of-exp p-body (cps-var-exp 'k%00))) p-bodies)
;  (cps-of-exp letrec-body k-exp))))

(define cps-of-letrec-exp
  (lambda (p-names b-varss p-bodies letrec-body k-exp)
    (define uninitialized (cps-const-exp -1))
    (let loop-newref-names ([names p-names])
      (if (null? names)
          (let loop-setref-names ([names p-names]
                                  [varss (map (lambda (b-vars) (append b-vars (list 'k%00))) b-varss)]
                                  [bodies (map (lambda (p-body) (cps-of-exp p-body (cps-var-exp 'k%00))) p-bodies)])
            (if (null? names)
                (cps-of-exp letrec-body k-exp)
                (cps-setref-exp (cps-var-exp (car names))
                                (cps-proc-exp (car varss)
                                              (car bodies))
                                (loop-setref-names (cdr names)
                                                   (cdr varss)
                                                   (cdr bodies)))))
          (cps-newref-exp uninitialized
                          (cps-proc-exp (list (car names))
                                        (loop-newref-names (cdr names))))))))



; cps-of-program : InpExp → TfExp
(define cps-of-program
  (lambda (pgm)
    (cases program
      pgm
      (a-program (exp1)
                 (cps-a-program (cps-of-exps (list exp1)
                                             (lambda (new-args) ;;; why this builder?
                                               (simple-exp->exp
                                                (car new-args)))))))))

(define transform (lambda (str)
                    (cps-of-program (scan&parse-cps-in str))))

(provide transform)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; test

(define str0
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
(check-equal? (value-of-cps-out-program (transform str0)) (num-val 551))

(define str1
  "let f = proc(x) x
   in (f 73)")
#|
newref(proc(x k) deref(x, k), proc(f) deref(f, proc(v0) (v0 73 proc(x) x)))
newref(proc(x k) deref(x, k), proc(f) deref(f, proc(v0) newref(33, proc(v1) (v0 v1 proc(x) x))))
|#
(check-equal? (value-of-cps-out-program (transform str1)) (num-val 73))

(define str2
  "let loc1 = 33
   in let loc2 = 44
      in let void = set loc1 = 22
         in -(loc1, loc2)")
(check-equal? (value-of-cps-out-program (transform str2)) (num-val -22))

#|
let loc1 = 33
in let loc2 = 44
   in let void = set loc1 = 22
      in -(loc1, loc2)

===============================================================
let loc1 = newref(33)
in let val = 44
   in let void = setref(loc1, 22)
      in -(deref(loc1), val)

newref(33, proc(loc1)
             let val1 = 44
             in setref(loc1, 22);
                deref(loc1, proc(val2)
                            -(val2, val1)))

===============================================================
let loc1 = newref(33)
    in let loc2 = newref(44)
       in let void = setref(loc1, 22)
          in -(deref(loc1), deref(loc2))

newref(33, proc(loc1)
              newref(44, proc(loc2)
                            setref(loc1, 22);
                            deref(loc1, proc (val1)
                                            deref(loc2, proc(val2)
                                                          -(val1, val2)))))
|#

(define str3
  "let x = 22
   in let f = proc (z) let zz = -(z, x)
                       in zz
      in -((f 66), (f 55))")

(check-equal? (value-of-cps-out-program (transform str3)) (num-val 11))

(define str4
  "let g = let counter = 0
           in proc (dummy)
                let void = set counter = -(counter, -1)
                in  counter
  in let a = (g 11)
     in let b = (g 11)
        in -(a,b)")
(check-equal? (value-of-cps-out-program (transform str4)) (num-val -1))

(define str5
  "
  letrec double(x)
          = if zero?(x) then 0 else -((double -(x, 1)), -2)
  in (double 6)
   ")
 (check-equal? (value-of-cps-out-program (transform str5)) (num-val 12))

(define str6
  "letrec foo() = (foo)
   in (foo)")
(transform str6)
#|
newref(-1, proc(foo) setref(foo, proc(k) deref(foo, proc(v0) (k v0))); deref(foo, proc(v1) (v1 proc(x) x)))
|#

(define str7
  "letrec foo(x) = (foo -(x, 1))
   in (foo 37)")
(transform str7)
#|
newref(-1,
       proc(foo)
         setref(foo,
                proc(x k00)
                  deref(foo,
                        proc(var6)
                          deref(x,
                                proc(var8)
                                newref(1,
                                       proc(var9)
                                         (proc(var7) (var6 var7 k00) -(var8, var9))))));
          deref(foo, proc(var10) newref(37, proc(var11) (var10 var11 proc(var5) var5))))

|#