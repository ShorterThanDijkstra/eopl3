#lang eopl
(require rackunit)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Procedure data type
; procedure : Var × Exp × Env → Proc
(define-datatype
  proc
  proc?
  (procedure (var identifier?)
             (body expression?)
             (saved-env environment?)))
; apply-procedure : Proc × ExpVal → ExpVal
(define apply-procedure
  (lambda (proc1 val)
    (cases proc
      proc1
      (procedure (var body saved-env)
                 (value-of body
                           (extend-env
                            var
                            (newref val)
                            saved-env))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Mutpair
; mutpair? : SchemeVal → Bool
(define mutpair?
  (lambda (v)
    (reference? v)))
; make-pair : ExpVal × ExpVal → MutPair
(define make-pair
  (lambda (val1 val2)
    (let ((ref1 (newref val1)))
      (let ((ref2 (newref val2)))
        ref1))))
; left : MutPair → ExpVal
(define left
  (lambda (p)
    (deref p)))
; right : MutPair → ExpVal
(define right
  (lambda (p)
    (deref (+ 1 p))))
; setleft : MutPair × ExpVal → Unspecified
(define setleft
  (lambda (p val)
    (setref! p val)))
; setright : MutPair × ExpVal → Unspecified
(define setright
  (lambda (p val)
    (setref! (+ 1 p) val)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal data type
(define-datatype expval
  expval?
  (num-val (value number?))
  (bool-val (boolean boolean?))
  (proc-val (proc proc?))
  (mutpair-val (pair mutpair?))
  )

(define expval->num
  (lambda (v)
    (cases expval v
      (num-val (num) num)
      (else (eopl:error 'expval->num "~s" v)))))

(define expval->bool
  (lambda (v)
    (cases expval v
      (bool-val (bool) bool)
      (else (eopl:error 'expval->bool "~s" v)))))

(define expval->proc
  (lambda (v)
    (cases expval v
      (proc-val (proc) proc)
      (else (eopl:error 'expval->proc "~s" v)))))

(define expval->mutpair
  (lambda (v)
    (cases expval v
      (mutpair-val (val) val)
      (else (eopl:error 'expval->mutpair "~s" v)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Store
; empty-store : () → Sto
(define empty-store (lambda () '()))
; usage: A Scheme variable containing the current state
; of the store. Initially set to a dummy value.

(define the-store 'uninitialized)

; get-store : () → Sto
(define get-store (lambda () the-store))

; initialize-store! : () → Unspecified
; usage: (initialize-store!) sets the-store to the empty store
(define initialize-store!
  (lambda () (set! the-store (empty-store))))

; reference? : SchemeVal → Bool
(define reference? (lambda (v) (integer? v)))

; newref : ExpVal → Ref
(define newref
  (lambda (val)
    (let ([next-ref (length the-store)])
      (set! the-store
            (append the-store (list val)))
      next-ref)))

; deref : Ref → ExpVal
(define deref
  (lambda (ref) (list-ref the-store ref)))

; setref! : Ref × ExpVal → Unspecified
; usage: sets the-store to a state like the original, but with
; position ref containing val.
(define setref!
  (lambda (ref val)
    (set!
     the-store
     (letrec
         ([setref-inner
           ; usage: returns a list like store1, except that
           ; position ref1 contains val.
           (lambda (store1 ref1)
             (cond
               [(null? store1)
                (eopl:error
                 "report-invalid-reference ~s"
                 ref
                 the-store)]
               [(zero? ref1)
                (cons val (cdr store1))]
               [else
                (cons (car store1)
                      (setref-inner
                       (cdr store1)
                       (- ref1 1)))]))])
       (setref-inner the-store ref)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Env
(define-datatype
  environment
  environment?
  (empty-env)
  (extend-env (var identifier?)
              (ref reference?)
              (env environment?))
  (extend-env-rec (p-names (list-of identifier?))
                  (b-vars (list-of identifier?))
                  (bodys (list-of expression?))
                  (env environment?)))

(define location
  (lambda (search names)
    (let loop ([pos 0] [names names])
      (cond
        [(null? names) #f]
        [(eqv? (car names) search) pos]
        [else (loop (+ pos 1) (cdr names))]))))

(define apply-env
  (lambda (env search-var)
    (cases
        environment
      env
      (empty-env ()
                 (eopl:error 'apply-env
                             "No binding for ~s"
                             search-var))
      (extend-env
       (bvar ref saved-env)
       (if (eqv? search-var bvar)
           ref
           (apply-env saved-env search-var)))
      (extend-env-rec
       (p-names b-vars p-bodies saved-env)
       (let ([n (location search-var p-names)])
         (if n
             (newref (proc-val
                      (procedure
                       (list-ref b-vars n)
                       (list-ref p-bodies n)
                       env)))
             (apply-env saved-env search-var)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Expression data type && Program
(define identifier?
  (lambda (exp)
    (and (symbol? exp) (not (eqv? exp 'lambda)))))

(define-datatype
  expression
  expression?
  (const-exp (num number?))
  (if-exp (exp1 expression?)
          (exp2 expression?)
          (exp3 expression?))
  (zero?-exp (exp1 expression?))
  (var-exp (var identifier?))
  (diff-exp (exp1 expression?) (exp2 expression?))
  (let-exp (var identifier?)
           (exp expression?)
           (body expression?))
  (letrec-exp (p-names (list-of identifier?))
              (b-vars (list-of identifier?))
              (p-bodies (list-of expression?))
              (letrec-body expression?))
  (proc-exp (var identifier?) (body expression?))
  (call-exp (rator expression?) (rand expression?))
  (assign-exp (var identifier?) (exp1 expression?))
  (seq-exp (exps (list-of expression?)))
  (newpair-exp (exp1 expression?)
               (exp2 expression?))
  (left-exp (exp1 expression?))
  (right-exp (exp1 expression?))
  (setleft-exp (exp1 expression?)
               (exp2 expression?))
  (setright-exp (exp1 expression?)
                (exp2 expression?))
  )

(define-datatype program
  program?
  (a-program (exp1 expression?)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter

; value-of : Exp × Env → ExpVal
(define value-of
  (lambda (exp env)
    (cases
        expression
      exp
      (const-exp (num) (num-val num))
      (var-exp (var) (deref (apply-env env var)))
      (diff-exp (exp1 exp2)
                (let ([val1 (value-of exp1 env)]
                      [val2 (value-of exp2 env)])
                  (let ([num1 (expval->num val1)]
                        [num2 (expval->num val2)])
                    (num-val (- num1 num2)))))
      (if-exp (exp1 exp2 exp3)
              (let ([val1 (value-of exp1 env)])
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      (zero?-exp (exp1)
                 (let ([val1 (value-of exp1 env)])
                   (let ([num1 (expval->num val1)])
                     (if (zero? num1)
                         (bool-val #t)
                         (bool-val #f)))))
      (let-exp
       (var exp1 body)
       (let ([val1 (value-of exp1 env)])
         (value-of
          body
          (extend-env var (newref val1) env))))
      (letrec-exp (proc-names bound-vars
                              proc-bodies
                              letrec-body)
                  (value-of letrec-body
                            (extend-env-rec
                             proc-names
                             bound-vars
                             proc-bodies
                             env)))
      (proc-exp
       (var body)
       (proc-val (procedure var body env)))
      (call-exp (rator rand)
                (let ([proc (expval->proc
                             (value-of rator env))]
                      [arg (value-of rand env)])
                  (apply-procedure proc arg)))
      (assign-exp (var exp1)
                  (begin
                    (setref! (apply-env env var)
                             (value-of exp1 env))
                    (num-val 27)))
      (seq-exp
       (exps)
       (if (null? exps)
           (eopl:error 'value-of " empty seq-exp")
           (let loop ([rest (cdr exps)]
                      [last-val
                       (value-of (car exps) env)])
             (if (null? rest)
                 last-val
                 (loop (cdr rest)
                       (value-of (car rest)
                                 env))))))
      (newpair-exp (exp1 exp2)
                   (let ((val1 (value-of exp1 env))
                         (val2 (value-of exp2 env)))
                     (mutpair-val (make-pair val1 val2))))
      (left-exp (exp1)
                (let ((val1 (value-of exp1 env)))
                  (let ((p1 (expval->mutpair val1)))
                    (left p1))))
      (right-exp (exp1)
                 (let ((val1 (value-of exp1 env)))
                   (let ((p1 (expval->mutpair val1)))
                     (right p1))))
      (setleft-exp (exp1 exp2)
                   (let ((val1 (value-of exp1 env))
                         (val2 (value-of exp2 env)))
                     (let ((p (expval->mutpair val1)))
                       (begin
                         (setleft p val2)
                         (num-val 82)))))
      (setright-exp (exp1 exp2)
                    (let ((val1 (value-of exp1 env))
                          (val2 (value-of exp2 env)))
                      (let ((p (expval->mutpair val1)))
                        (begin
                          (setright p val2)
                          (num-val 83)))))
      )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;run
(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter
      (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define the-grammar-spec
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression (identifier) var-exp)
    (expression
     ("-" "(" expression "," expression ")")
     diff-exp)
    (expression ("zero?" "(" expression ")")
                zero?-exp)
    (expression ("if" expression
                      "then"
                      expression
                      "else"
                      expression)
                if-exp)
    (expression ("let" identifier
                       "="
                       expression
                       "in"
                       expression)
                let-exp)
    (expression ("letrec" (arbno identifier
                                 "("
                                 identifier
                                 ")"
                                 "="
                                 expression)
                          "in"
                          expression)
                letrec-exp)
    (expression
     ("proc" "(" identifier ")" expression)
     proc-exp)
    (expression ("(" expression expression ")")
                call-exp)
    (expression ("set" identifier "=" expression)
                assign-exp)
    (expression
     ("begin" (separated-list expression ";")
              "end")
     seq-exp)
    (expression
     ("pair" "(" expression "," expression ")")
     newpair-exp)
    (expression
     ("left" "(" expression ")")
     left-exp)
    (expression
     ("right" "(" expression ")")
     right-exp)
    (expression
     ("setleft" "(" expression "," expression ")")
     setleft-exp)
    (expression
     ("setright" "(" expression "," expression ")")
     setright-exp)
    ))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec
                             the-grammar-spec))

(define init-env
  (lambda ()
    (extend-env 'true
                (newref (bool-val #t))
                (extend-env 'false
                            (newref (bool-val #f))
                            (empty-env)))))

; value-of-program : Program → ExpVal
(define value-of-program
  (lambda (pgm)
    (initialize-store!)
    (cases program
      pgm
      (a-program
       (exp1)
       (value-of exp1 (init-env))))))

(define run
  (lambda (str)
    (value-of-program (scan&parse str))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;test
(define str1
  "let glo = pair(11,22)
       in let f = proc (loc)
                   let d1 = setright(loc, left(loc))
                   in let d2 = setleft(glo, 99)
                      in -(left(loc),right(loc))
          in (f glo)")

(check-equal? (run str1) (num-val 88))