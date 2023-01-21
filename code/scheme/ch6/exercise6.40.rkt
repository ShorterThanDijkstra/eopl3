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
    (expression (identifier) var-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("+" "(" (separated-list expression ",") ")") sum-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression
     ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" expression)
               "in"
               expression)
     letrec-exp)
    (expression ("proc" "(" (arbno identifier) ")" expression) proc-exp)
    (expression ("print" "(" expression ")") print-exp)
    (expression ("newref" "(" expression ")") newref-exp)
    (expression ("deref" "(" expression ")") deref-exp)
    (expression ("setref" "(" expression "," expression ")") setref-exp)
    (expression ("letcc" identifier "in" expression) letcc-exp)
    (expression ("throw" expression "to" expression) throw-exp)
    (expression ("try" expression "catch" "(" identifier ")" expression)
                try-exp)
    (expression ("raise" expression) raise-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)))

(define scan&parse-cps-in
  (sllgen:make-string-parser cps-in-lexical-spec cps-in-grammar-spec))

(sllgen:make-define-datatypes cps-in-lexical-spec cps-in-grammar-spec)

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
  (lambda (exps err builder)
    (let cps-of-rest ([exps exps])
      ;   cps-of-rest : Listof(InpExp) → TfExp
      (let ([pos (list-index (lambda (exp) (not (inp-exp-simple? exp))) exps)])
        (if (not pos)
            (builder (map cps-of-simple-exp exps))
            (let ([ok-var (fresh-identifier 'var)]
                  [err-var (fresh-identifier 'err)])
              (cps-of-exp (list-ref exps pos)
                          (cps-proc-exp
                           (list ok-var)
                           (cps-of-rest
                            (list-set exps pos (var-exp ok-var))))
                          (cps-proc-exp
                           (list err-var)
                           (make-send-to-cont err (cps-var-exp err-var))) )))))))

; inp-exp-simple? : InpExp → Bool
(define inp-exp-simple?
  (lambda (exp)
    (cases
        expression
      exp
      (const-exp (num) #t)
      (var-exp (var) #t)
      (diff-exp (exp1 exp2) (and (inp-exp-simple? exp1) (inp-exp-simple? exp2)))
      (zero?-exp (exp1) (inp-exp-simple? exp1))
      (proc-exp (ids exp) #t)
      (sum-exp (exps) (every? inp-exp-simple? exps))
      (else #f))))

; cps-of-exp : InpExp × SimpleExp → TfExp
(define cps-of-exp
  (lambda (exp ok err)
    (cases
        expression
      exp
      (const-exp (num) (make-send-to-cont ok (cps-const-exp num)))
      (var-exp (var) (make-send-to-cont ok (cps-var-exp var)))
      (proc-exp (vars body)
                (make-send-to-cont ok
                                   (cps-proc-exp (append vars (list 'k%00 'h%00))
                                                 (cps-of-exp body (cps-var-exp 'k%00)
                                                             (cps-var-exp 'h%00)))))
      (zero?-exp (exp1) (cps-of-zero?-exp exp1 ok err))
      (diff-exp (exp1 exp2) (cps-of-diff-exp exp1 exp2 ok err))
      (sum-exp (exps) (cps-of-sum-exp exps ok err))
      (if-exp (exp1 exp2 exp3) (cps-of-if-exp exp1 exp2 exp3 ok err))
      (let-exp (var exp1 body) (cps-of-let-exp var exp1 body ok err))
      (letrec-exp (p-names b-varss p-bodies letrec-body)
                  (cps-of-letrec-exp p-names b-varss p-bodies letrec-body ok err))
      ;; new for cps-side-effects-lang
      ;; Page: 228
      (print-exp (rator)
                 (cps-of-exps (list rator)
                              err
                              (lambda (simples)
                                (cps-print-exp
                                 (car simples)
                                 (make-send-to-cont ok (cps-const-exp 38))))))
      ;; Page 231
      (newref-exp (exp1)
                  (cps-of-exps (list exp1)
                               err
                               (lambda (simples)
                                 (cps-newref-exp (car simples) ok))))
      (deref-exp (exp1)
                 (cps-of-exps (list exp1)
                              err
                              (lambda (simples)
                                (cps-deref-exp (car simples) ok))))
      (setref-exp (exp1 exp2)
                  (cps-of-exps
                   (list exp1 exp2)
                   err
                   (lambda (simples)
                     (cps-setref-exp
                      (car simples)
                      (cadr simples)
                      ;; the third argument will be evaluated tail-recursively.
                      ;; returns 23, just like in explicit-refs
                      (make-send-to-cont ok (cps-const-exp 23))))))
      (letcc-exp (var body) (cps-of-letcc-exp var body ok err))
      (throw-exp (exp1 exp2) (cps-of-throw-exp exp1 exp2 ok err))
      (try-exp (exp1 var handler-exp)
               (cps-of-try-exp exp1 var handler-exp ok err))
      (raise-exp (exp1) (cps-of-raise-exp exp1 ok err))
      (call-exp (rator rands) (cps-of-call-exp rator rands ok err)))))

(define cps-of-try-exp
  (lambda (exp1 var handler-exp ok err)
    (cps-of-exps (list exp1)
                 (cps-proc-exp (list var)
                               (cps-of-exp handler-exp ok err))
                 (lambda (simples)
                   (make-send-to-cont ok (car simples))))))

(define cps-of-raise-exp
  (lambda (exp1 ok err)
    (cps-of-exp exp1 err err)))

(define cps-of-letcc-exp
  (lambda (var body ok err)
    (cps-let-exp var ok (cps-of-exp body (cps-var-exp var) err))))

(define cps-of-throw-exp
  (lambda (exp1 exp2 ok err)
    (cps-of-exps (list exp1 exp2)
                 err
                 (lambda (simples)
                   (cps-call-exp (cadr simples) (list (car simples)))))))

; cps-of-sum-exp : Listof(InpExp) × SimpleExp → TfExp
(define cps-of-sum-exp
  (lambda (exps ok err)
    (cps-of-exps exps
                 err
                 (lambda (simples)
                   (make-send-to-cont ok (cps-sum-exp simples))))))

; cps-of-simple-exp : InpExp → SimpleExp
; usage: assumes (inp-exp-simple? exp).
(define cps-of-simple-exp
  (lambda (exp)
    (cases expression exp
      (const-exp (num) (cps-const-exp num))
      (var-exp (var) (cps-var-exp var))
      (diff-exp (exp1 exp2) (cps-diff-exp (cps-of-simple-exp exp1) (cps-of-simple-exp exp2)))
      (zero?-exp (exp1) (cps-zero?-exp (cps-of-simple-exp exp1)))
      (proc-exp (ids exp) (cps-proc-exp (append ids (list 'k%00 'h%00))
                                        (cps-of-exp exp (cps-var-exp 'k%00) (cps-var-exp 'h%00))))
      (sum-exp (exps) (cps-sum-exp (map cps-of-simple-exp exps)))
      (else (report-invalid-exp-to-cps-of-simple-exp exp)))))
; cps-of-call-exp : InpExp × Listof(InpExp) × SimpleExp → TfExp
(define cps-of-call-exp
  (lambda (rator rands ok err)
    (cps-of-exps (cons rator rands)
                 err
                 (lambda (simples)
                   (cps-call-exp (car simples)
                                 (append (cdr simples) (list ok err)))))))

; cps-of-zero?-exp : InpExp × SimpleExp → TfExp
(define cps-of-zero?-exp
  (lambda (exp1 ok err)
    (cps-of-exps (list exp1)
                 err
                 (lambda (simples)
                   (make-send-to-cont ok (cps-zero?-exp (car simples)))))))

; cps-of-diff-exp : InpExp × InpExp × SimpleExp → TfExp
(define cps-of-diff-exp
  (lambda (exp1 exp2 ok err)
    (cps-of-exps
     (list exp1 exp2)
     err
     (lambda (simples)
       (make-send-to-cont ok (cps-diff-exp (car simples) (cadr simples)))))))

; cps-of-if-exp : InpExp × InpExp × InpExp × SimpleExp → TfExp
(define cps-of-if-exp
  (lambda (exp1 exp2 exp3 ok err)
    (cps-of-exps (list exp1)
                 err
                 (lambda (simples)
                   (cps-if-exp (car simples)
                               (cps-of-exp exp2 ok err)
                               (cps-of-exp exp3 ok err))))))


(define cps-of-let-exp
  (lambda (id rhs body ok err)
    (cps-of-exp (call-exp (proc-exp (list id) body) (list rhs)) ok err)))

; cps-of-letrec-exp :
; Listof(Listof(Var)) * Listof(InpExp) * InpExp * SimpleExp -> TfExp
(define cps-of-letrec-exp
  (lambda (p-names b-varss p-bodies letrec-body ok err)
    (cps-letrec-exp
     p-names
     (map (lambda (b-vars) (append b-vars (list 'k%00))) b-varss)
     (map (lambda (p-body) (cps-of-exp p-body (cps-var-exp 'k%00) err)) p-bodies)
     (cps-of-exp letrec-body ok err))))

; cps-of-program : InpExp → TfExp
(define cps-of-program
  (lambda (pgm)
    (cases program
      pgm
      (a-program (exp1)
                 (cps-a-program
                  (cps-of-exps (list exp1)
                               (let ([err-var (fresh-identifier 'err)])
                                 (cps-proc-exp (list err-var) (simple-exp->exp (cps-var-exp err-var))))
                               (lambda (new-args)
                                 (simple-exp->exp (car new-args)))))))))

(define transform (lambda (str) (cps-of-program (scan&parse-cps-in str))))

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

(define str1 "let f = proc(x) x
   in (f 73)")

(check-equal? (value-of-cps-out-program (transform str1)) (num-val 73))
(define str2
  "let loc1 = newref(33)
   in let loc2 = newref(44)
      in let void = setref(loc1, 22)
         in -(deref(loc1), 1)")
(check-equal? (value-of-cps-out-program (transform str2)) (num-val 21))

(define str3
  "let x = newref(22)
   in let f = proc (z) let zz = newref(-(z,deref(x)))
                       in deref(zz)
      in -((f 66), (f 55))")
(check-equal? (value-of-cps-out-program (transform str3)) (num-val 11))

(define str4
  "let g = let counter = newref(0)
           in proc (dummy)
                let void = setref(counter, -(deref(counter), -1))
                in  deref(counter)
  in let a = (g 11)
     in let b = (g 11)
        in -(a,b)")
(check-equal? (value-of-cps-out-program (transform str4)) (num-val -1))

(define str5
  "
  let x = 114
  in -(114514,
       letcc y
       in let f = proc(z) -(z, 514)
          in throw (f x) to y)
  ")
#|
(proc(x k) let y = proc(v0) (k -(114514, v0))
           in (proc(f k) (f x proc(v1) (y v1)) proc(z k) (k -(z, 514))
              y)
114
proc(x) x)
|#
(check-equal? (value-of-cps-out-program (transform str5)) (num-val 114914))

#|
(define fact
  (lambda (n)
    (if (zero? n)
        1
        (* n (fact (- n 1))))))

(define fact/k
  (lambda (n k)
    (if (zero? n)
        (k 1)
        (fact/k (- n 1)
                (lambda (v0)
                  (k (* n v0)))))))

(define fact/k
  (lambda (n ok err)
    (if (zero? n)
        (ok 1)
        (fact/k (- n 1)
                (lambda (v0)
                  (if (= v0 3628800)
                      (err 'stack-overflow)
                      (ok (* n v0))))
                (lambda (v0)
                  (begin (display v0)
                         (newline)
                         (err v0)))))))

(define ok (lambda (x) x))

(define err
  (lambda (msg)
    (display "error: ")
    (display msg)
    (newline)))
|#

(define str6
  "
  try let x = raise 114
      in -(x, 514)
  catch (e) e
  ")
(check-equal? (value-of-cps-out-program (transform str6)) (num-val 114))

(define str7
  "try
     try raise -73
     catch (e) raise -37
  catch (e) e
  ")
(check-equal? (value-of-cps-out-program (transform str7)) (num-val -37))

(define str8
  "let foo = proc() raise -7
   in let bar = proc() try (foo) catch(e) raise -2
      in let baz = proc() try (bar) catch(e) raise -3
         in try (baz) catch(e) e")
(check-equal? (value-of-cps-out-program (transform str8)) (num-val -3))
