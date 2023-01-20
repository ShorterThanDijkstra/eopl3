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

(define list-sub
  (lambda (lst1 lst2)
    (cond [(null? lst1) '()]
          [(memq (car lst1) lst2)
           (list-sub (cdr lst1) lst2)]
          [else (cons (car lst1)
                      (list-sub (cdr lst1) lst2))])))

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
(define immutable-var?
  (lambda (var exp)
    (cases expression
      exp
      (const-exp (num) #t)
      (var-exp (var) #t)
      (diff-exp (exp1 exp2) (and (immutable-var? var exp1)
                                 (immutable-var? var exp2)))
      (sum-exp (exps) (every? (lambda (exp) (immutable-var? var exp)) exps))
      (if-exp (exp1 exp2 exp3) (and (immutable-var? var exp1)
                                    (immutable-var? var exp2)
                                    (immutable-var? var exp3)))
      (zero?-exp (exp1) (immutable-var? var exp1))
      (let-exp (var1 rhs body) (if (immutable-var? var rhs)
                                   (if (eqv? var var1)
                                       #t ; let binding considered immutable
                                       (immutable-var? var body))
                                   #f))
      (letrec-exp (proc-names bound-varss proc-bodies letrec-body)
                  (let loop-procs ([varss bound-varss]
                                   [bodies proc-bodies])
                    (if (null? varss)
                        (immutable-var? var letrec-body)
                        (if (memq var (car varss))
                            #t ; procedure arguments considered immutable
                            (and (immutable-var? var (car bodies))
                                 (loop-procs (cdr varss) (cdr bodies)))))))
      (proc-exp (vars body) (if (memq var vars)
                                #t ; procedure arguments considered immutable
                                (immutable-var? var body)))

      (print-exp (exp1) (immutable-var? var exp1))
      (assign-exp (var1 exp1) (if (eqv? var1 var)
                                  #f
                                  (immutable-var? var exp1)))
      (call-exp (rator rands) (and (immutable-var? var rator)
                                   (every? (lambda (rand) (immutable-var? var rand)) rands))))))

; make-send-to-cont : SimpleExp × SimpleExp → TfExp
(define make-send-to-cont
  (lambda (k-exp simple-exp) (cps-call-exp k-exp (list simple-exp))))

(define report-invalid-exp-to-cps-of-simple-exp
  (lambda (exp)
    (eopl:error 'cps-simple-of-exp
                "non-simple expression to cps-of-simple-exp: ~s"
                exp)))

; cps-of-exps : Listof(InpExp)× Listof(Symbol) × (Listof(InpExp) → TfExp) → TfExp
(define cps-of-exps
  (lambda (exps mutables builder)
    (let cps-of-rest ((exps exps) (acc '()))
      ; cps-of-rest : Listof(InpExp) × Listof(SimpleExp) → TfExp
      (cond
        ((null? exps) (builder (reverse acc)))
        ((inp-exp-simple? (car exps) mutables)
         (cps-of-rest (cdr exps)
                      (cons
                       (cps-of-simple-exp (car exps) mutables)
                       acc)))
        (else
         (let ((var (fresh-identifier 'var)))
           (cps-of-exp (car exps)
                       mutables
                       (cps-proc-exp (list var)
                                     (cps-of-rest (cdr exps)
                                                  (cons
                                                   (cps-of-simple-exp (var-exp var) mutables)
                                                   acc))))))))))

; inp-exp-simple? : InpExp × Listof(Symbol) → Bool
(define inp-exp-simple?
  (lambda (exp mutables)
    (cases
        expression
      exp
      (const-exp (num) #t)
      (var-exp (var) (not (memq var mutables)))
      (diff-exp (exp1 exp2) (and (inp-exp-simple? exp1 mutables) (inp-exp-simple? exp2 mutables)))
      (zero?-exp (exp1) (inp-exp-simple? exp1 mutables))
      (proc-exp (ids exp) #t)
      (sum-exp (exps) (every? (lambda (exp) (inp-exp-simple? exp mutables)) exps))
      (else #f))))

; cps-of-exp : InpExp × Listof(Symbol) × SimpleExp → TfExp
(define cps-of-exp
  (lambda (exp mutables k-exp)
    (cases
        expression
      exp
      (const-exp (num) (make-send-to-cont k-exp (cps-const-exp num)))
      (var-exp (var) (cps-of-var-exp var mutables k-exp))
      (proc-exp (vars body) (cps-of-proc-exp vars body mutables k-exp))
      (zero?-exp (exp1) (cps-of-zero?-exp exp1 mutables k-exp))
      (diff-exp (exp1 exp2) (cps-of-diff-exp exp1 exp2 mutables k-exp))
      (sum-exp (exps) (cps-of-sum-exp exps mutables k-exp))
      (if-exp (exp1 exp2 exp3) (cps-of-if-exp exp1 exp2 exp3 mutables k-exp))
      (let-exp (var exp1 body) (cps-of-let-exp var exp1 body mutables k-exp))
      (letrec-exp (p-names b-varss p-bodies letrec-body)
                  (cps-of-letrec-exp p-names b-varss p-bodies letrec-body mutables k-exp))
      (print-exp (rator) (cps-of-print-exp rator mutables k-exp))
      (assign-exp (var exp1) (cps-of-assign-exp var exp1 mutables k-exp))
      (call-exp (rator rands) (cps-of-call-exp rator rands mutables k-exp)))))

(define cps-of-proc-exp
  (lambda (vars body mutables k-exp)
    (make-send-to-cont
     k-exp
     (cps-proc-exp (append vars (list 'k%00))
                   (cps-of-exp body (list-sub mutables vars) (cps-var-exp 'k%00))))))

(define cps-of-var-exp
  (lambda (var mutables k-exp)
    (if (memq var mutables)
        (cps-deref-exp (cps-var-exp var) k-exp)
        (make-send-to-cont k-exp (cps-var-exp var)))))

(define cps-of-assign-exp
  (lambda (var exp1 mutables k-exp)
    (cps-of-exps (list exp1)
                 mutables
                 (lambda (simples)
                   (cps-setref-exp (cps-var-exp var)
                                   (car simples)
                                   (make-send-to-cont k-exp (cps-const-exp 23)))))))

(define cps-of-print-exp
  (lambda (rator mutables k-exp)
    (cps-of-exps (list rator)
                 mutables
                 (lambda (simples)
                   (cps-print-exp
                    (car simples)
                    (make-send-to-cont k-exp (cps-const-exp 38)))))))

; cps-of-sum-exp : Listof(InpExp) × Listof(Symbol) × SimpleExp → TfExp
(define cps-of-sum-exp
  (lambda (exps mutables k-exp)
    (cps-of-exps exps
                 mutables
                 (lambda (simples)
                   (make-send-to-cont k-exp (cps-sum-exp simples))))))

; cps-of-simple-exp : InpExp × Listof(Symbol) → SimpleExp
; usage: assumes (inp-exp-simple? exp).
(define cps-of-simple-exp
  (lambda (exp mutables)
    (cases
        expression
      exp
      (const-exp (num) (cps-const-exp num))
      (var-exp (var) (cps-var-exp var))
      (diff-exp (exp1 exp2)
                (cps-diff-exp (cps-of-simple-exp exp1 mutables) (cps-of-simple-exp exp2 mutables)))
      (zero?-exp (exp1) (cps-zero?-exp (cps-of-simple-exp exp1 mutables)))
      (proc-exp (ids body)
                (cps-proc-exp (append ids (list 'k%00))
                              (cps-of-exp body mutables (cps-var-exp 'k%00))))
      (sum-exp (exps) (cps-sum-exp (map (lambda (exp) (cps-of-simple-exp exp mutables)) exps)))
      (else (report-invalid-exp-to-cps-of-simple-exp exp)))))

; cps-of-call-exp : InpExp × Listof(InpExp) × Listof(Symbol) × SimpleExp → TfExp
;;; Function arguments are immutable by default.
;;; We could do mutability analysis for function arguments, but it is more complicated.
(define cps-of-call-exp
  (lambda (rator rands mutables k-exp)
    (cps-of-exps (cons rator rands)
                 mutables
                 (lambda (simples)
                   (cps-call-exp (car simples)
                                 (append (cdr simples) (list k-exp)))))))

; cps-of-zero?-exp : InpExp × Listof(Symbol) × SimpleExp → TfExp
(define cps-of-zero?-exp
  (lambda (exp1 mutables k-exp)
    (cps-of-exps (list exp1)
                 mutables
                 (lambda (simples)
                   (make-send-to-cont k-exp (cps-zero?-exp (car simples)))))))

; cps-of-diff-exp : InpExp × InpExp × Listof(Symbol) × SimpleExp → TfExp
(define cps-of-diff-exp
  (lambda (exp1 exp2 mutables k-exp)
    (cps-of-exps
     (list exp1 exp2)
     mutables
     (lambda (simples)
       (make-send-to-cont k-exp (cps-diff-exp (car simples) (cadr simples)))))))

; cps-of-if-exp : InpExp × InpExp × InpExp × Listof(Symbol) × SimpleExp → TfExp
(define cps-of-if-exp
  (lambda (exp1 exp2 exp3 mutables k-exp)
    (cps-of-exps (list exp1)
                 mutables
                 (lambda (simples)
                   (cps-if-exp (car simples)
                               (cps-of-exp exp2 mutables k-exp)
                               (cps-of-exp exp3 mutables k-exp))))))

; cps-of-let-exp : Var × InpExp × InpExp × Listof(Symbol) × SimpleExp → TfExp
;;; should change to procedure call?
(define cps-of-let-exp
  (lambda (id rhs body mutables k-exp)
    (let ([is-immutable (immutable-var? id body)])
      (let ([new-mutables (if is-immutable mutables (cons id mutables))])
        (let ([builder (if is-immutable
                           (lambda (simples)
                             (cps-let-exp id
                                          (car simples)
                                          (cps-of-exp body new-mutables k-exp)))
                           (lambda (simples)
                             (cps-newref-exp  (car simples)
                                              (cps-proc-exp (list id)
                                                            (cps-of-exp body new-mutables k-exp)))))])
          (cps-of-exps (list rhs) new-mutables builder))))))

; cps-of-letrec-exp :
; Listof(Listof(Var)) × Listof(InpExp) × InpExp × Listof(Symbol) × SimpleExp -> TfExp
;;; procedure variables considered immutable
(define cps-of-letrec-exp
  (lambda (p-names b-varss p-bodies letrec-body mutables k-exp)
    (cps-letrec-exp
     p-names
     (map (lambda (b-vars) (append b-vars (list 'k%00))) b-varss)
     (map (lambda (b-vars p-body)
            (cps-of-exp p-body (list-sub mutables b-vars) (cps-var-exp 'k%00)))
           b-varss
          p-bodies)
     (cps-of-exp letrec-body mutables k-exp))))

; cps-of-program : InpExp → TfExp
(define cps-of-program
  (lambda (pgm)
    (cases program
      pgm
      (a-program (exp1)
                 (cps-a-program (cps-of-exps (list exp1)
                                             '()
                                             (lambda (new-args)
                                               (simple-exp->exp
                                                (car new-args)))))))))

(define transform (lambda (str)
                    (cps-of-program (scan&parse-cps-in str))))

(provide transform)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; test

(define str0
  "let x = 33
   in let y = 55
      in let void = set y = 66
         in -(x, y)")
#|
let x = 33
in let y = 55
   in let void = set y = 66
      in -(x, y)


let x = 33
in newref(55,
          proc(y)
            setref(y, 66);
            deref(y, proc(v0)
                       -(x, v0)))
|#
(check-equal? (value-of-cps-out-program (transform str0)) (num-val -33))

(define str1
  "let x = 3
   in let y = 5
      in let f = proc(x) let void = set y = +(x, 3, y)
                        in y
         in  (f x)")
(check-equal? (value-of-cps-out-program (transform str1)) (num-val 11))

(define str2
  "let f = proc(x) set x = 73
   in (f 37)")
; (value-of-cps-out-program (transform str2)) ; should fail

(define str3
  "let x = 3
   in let y = 0
      in letrec dec3(n) = if zero?(n)
                          then 37
                          else let void = set y = -(y, -(0, 2))
                               in (dec3 -(n, x))
         in let ignore = (dec3 39)
            in y")
(check-equal? (value-of-cps-out-program (transform str3)) (num-val 26))

(define str4
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
(check-equal? (value-of-cps-out-program (transform str4)) (num-val 551))

(define str5
  "let loc1 = 33
   in let loc2 = 44
      in let void = set loc1 = 22
         in -(loc1, loc2)")
(check-equal? (value-of-cps-out-program (transform str5)) (num-val -22))

(define str6
  "
  letrec double(x)
          = if zero?(x) then 0 else -((double -(x, 1)), -2)
  in (double 6)
   ")
(check-equal? (value-of-cps-out-program (transform str6)) (num-val 12))

(define str7
  "let x = 37
   in let void = set x = 73
      in let f = proc(x) set x = 17
         in (f x)")
(value-of-cps-out-program (transform str7)) ;;; should fail
   