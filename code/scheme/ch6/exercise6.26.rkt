#lang eopl
(require "CPS-OUT.rkt")
(require rackunit)
(require racket/format)
(require racket/string)
(require rackunit)

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
;;; CPS In
(define cps-in-lexical-spec
  '([whitespace (whitespace) skip]
    [comment ("%" (arbno (not #\newline))) skip]
    [identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol]
    [number (digit (arbno digit)) number]
    [number ("-" digit (arbno digit)) number]))

(define cps-in-grammar
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("+" "(" (separated-list expression ",") ")") sum-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression
     ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" expression)
               "in"
               expression)
     letrec-exp)
    (expression (identifier) var-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("proc" "(" (arbno identifier) ")" expression) proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)))

(sllgen:make-define-datatypes cps-in-lexical-spec cps-in-grammar)

(define scan&parse-cps-in
  (sllgen:make-string-parser cps-in-lexical-spec cps-in-grammar))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Converter
#|
(K simple-exp) => cps-call-exp
(proc(var) T simple-exp)
|#
; replace-simple : SimpleExp -> Symbol -> SimpleExp -> ListOf(Symbol) -> SimpleExp
(define replace-simple
  (lambda (simple old new bounds)
    (cases simple-expression
      simple
      (cps-const-exp (num) simple)
      (cps-var-exp (var) (if (memq var bounds)
                             simple
                             (if (eqv? old var)
                                  new
                                  simple)))
      (cps-diff-exp (exp1 exp2)
                    (cps-diff-exp (replace-simple exp1 old new bounds)
                                  (replace-simple exp2 old new bounds)))
      (cps-sum-exp (exps) (cps-sum-exp (map (lambda (exp) (replace exp old new bounds)) exps)))
      (cps-zero?-exp (exp1) (cps-zero?-exp (replace-simple exp1 old new bounds)))
      (cps-proc-exp (vars body) (cps-proc-exp vars (replace body old new (append vars bounds)))))))

; replace : TfExp -> Symbol -> SimpleExp  -> ListOf(Symbol) -> TfExp
(define replace
  (lambda (exp old new bounds)
    (cases
        tfexp
      exp
      (simple-exp->exp (simple)
                       (simple-exp->exp (replace-simple simple old new bounds)))
      (cps-let-exp (var rhs body)
                   (cps-let-exp var
                                (replace-simple rhs old new bounds)
                                (replace body old new (cons var bounds))))
      (cps-letrec-exp (p-names b-varss p-bodies letrec-body)
                      (let ((new-bounds (append p-names bounds)))
                        (let ((new-p-bodies (map (lambda (b-vars p-body)
                                                   (replace p-body old new (append b-vars new-bounds)))
                                                 b-varss p-bodies)))
                          (cps-letrec-exp p-names b-varss new-p-bodies
                                          (replace letrec-body old new new-bounds)))))
      (cps-if-exp (simple1 body1 body2)
                  (cps-if-exp (replace-simple simple1 old new bounds)
                              (replace body1 old new bounds)
                              (replace body2 old new bounds)))
      (cps-call-exp (rator rands) (cps-call-exp (replace-simple rator old new bounds)
                                                (map (lambda (rand) (replace-simple rand old new bounds) rands)))))))


; make-send-to-cont : SimpleExp × SimpleExp → TfExp
(define make-send-to-cont
  (lambda (k-exp simple-exp)
    (cases simple-expression k-exp
      (cps-var-exp (var) (cps-call-exp k-exp (list simple-exp)))
      (cps-proc-exp (vars body)
                    (replace body (car vars) simple-exp '()))
      (else (eopl:error 'make-send-to-cont "~s" k-exp)))))

(define report-invalid-exp-to-cps-of-simple-exp
  (lambda (exp)
    (eopl:error 'cps-simple-of-exp
                "non-simple expression to cps-of-simple-exp: ~s"
                exp)))

; cps-of-exps : Listof(InpExp) × (Listof(InpExp) → TfExp) → TfExp
(define cps-of-exps
  (lambda (exps builder)
    (let cps-of-rest ([exps exps])
      ;   cps-of-rest : Listof(InpExp) → TfExp
      (let ([pos (list-index (lambda (exp) (not (inp-exp-simple? exp))) exps)])
        (if (not pos)
            (builder (map cps-of-simple-exp exps))
            (let ([var (fresh-identifier 'var)])
              (cps-of-exp (list-ref exps pos)
                          (cps-proc-exp
                           (list var)
                           (cps-of-rest
                            (list-set exps pos (var-exp var)))))))))))

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
  (lambda (exp k-exp)
    (cases
        expression
      exp
      (const-exp (num) (make-send-to-cont k-exp (cps-const-exp num)))
      (var-exp (var) (make-send-to-cont k-exp (cps-var-exp var)))
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
      (call-exp (rator rands) (cps-of-call-exp rator rands k-exp)))))

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
(define cps-of-call-exp
  (lambda (rator rands k-exp)
    (cps-of-exps (cons rator rands)
                 (lambda (simples)
                   (cps-call-exp (car simples)
                                 (append (cdr simples) (list k-exp)))))))

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
(define cps-of-let-exp
  (lambda (id rhs body k-exp)
    (cps-of-exp (call-exp (proc-exp (list id) body) (list rhs)) k-exp)))

; cps-of-letrec-exp :
; Listof(Listof(Var)) * Listof(InpExp) * InpExp * SimpleExp -> TfExp
(define cps-of-letrec-exp
  (lambda (p-names b-varss p-bodies letrec-body k-exp)
    (cps-letrec-exp
     p-names
     (map (lambda (b-vars) (append b-vars (list 'k%00))) b-varss)
     (map (lambda (p-body) (cps-of-exp p-body (cps-var-exp 'k%00))) p-bodies)
     (cps-of-exp letrec-body k-exp))))

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
(transform str0)

(define str1
  "let f = proc(x) x
   in (f 73)")
(check-equal? (value-of-cps-out-program (transform str1)) (num-val 73))

(define str2
  "let f = proc(x) 0
   in let g = proc(x y) 0
      in let x = 73
         in let y = 37
         in +(22, (f x), 33, (g y 37))")
(check-equal? (value-of-cps-out-program (transform str2)) (num-val 55))

(unparse (transform "+(22, (f x), 33, (g y 37))"))
; "(f x proc(v0) (g y 37 proc(v1) +(22, v0, 33, v1)))"

