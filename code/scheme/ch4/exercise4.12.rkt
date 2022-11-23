#lang eopl
(require rackunit)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Procedure data type
; procedure : Var × Exp × Env → Proc
(define-datatype proc proc?
  (procedure
   (var identifier?)
   (body expression?)
   (saved-env environment?)))
; apply-procedure : Proc × ExpVal → ExpVal
(define apply-procedure
  (lambda (proc1 val store)
    (cases proc proc1
      (procedure (var body saved-env)
                 (value-of body (extend-env var val saved-env) store)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal data type
(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val (proc proc?))
  (ref-val
   (val reference?))
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

(define expval->ref
  (lambda (v)
    (cases expval v
      	(ref-val (ref) ref)
      	(else ((eopl:error 'expval->ref "~s" v))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Store
(define store? (list-of expval?))

; empty-store : () → Sto
(define empty-store
  (lambda () '()))
; usage: A Scheme variable containing the current state
; of the store. Initially set to a dummy value.

; initialize-store! : () → Unspecified
; usage: (initialize-store!) sets the-store to the empty store
(define initialize-store!
  (lambda ()
    (empty-store)))

; reference? : SchemeVal → Bool
(define reference?
  (lambda (v)
    (integer? v)))

; newref : ExpVal × Sto → Sto × Ref
(define newref
  (lambda (val store)
    (let ((next-ref (length store)))
      (list
       (append store (list val))
       next-ref))))

; deref : Ref × Sto → Sto × ExpVal
(define deref
  (lambda (ref store)
    (list
    store
     (list-ref store ref))))

; setref! : Ref × ExpVal × Sto → Sto × Unspecified
; usage: sets the-store to a state like the original, but with
; position ref containing val.
(define setref!
  (lambda (ref val store)
    (letrec ((loop (lambda (ref store)
                     (cond
                       ((null? store)
                        (eopl:error "report-invalid-reference ~s" ref store))
                       ((zero? ref)
                        (cons val (cdr store)))
                       (else
                        (cons
                         (car store)
                         (loop (- ref 1)  (cdr store))))))))
      (list (loop ref store) val))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Env
(define empty-env-record
  (lambda ()
    '()))

(define extended-env-record
  (lambda (sym val old-env)
    (cons (list sym val) old-env)))

(define empty-env-record? null?)

(define environment?
  (lambda (x)
    (or (empty-env-record? x)
        (and (pair? x)
             (symbol? (car (car x)))
             (expval? (cadr (car x)))
             (environment? (cdr x))))))

(define extended-env-record->sym
  (lambda (r)
    (car (car r))))

(define extended-env-record->val
  (lambda (r)
    (cadr (car r))))

(define extended-env-record->old-env
  (lambda (r)
    (cdr r)))

(define empty-env
  (lambda ()
    (empty-env-record)))

(define empty-env?
  (lambda (x)
    (empty-env-record? x)))

(define extend-env
  (lambda (sym val old-env)
    (extended-env-record sym val old-env)))

(define extend-env-list
  (lambda (syms vals old-env)
    (if (null? syms)
        old-env
        (extend-env-list (cdr syms) (cdr vals)
                         (extend-env (car syms) (car vals) old-env)))))

(define apply-env
  (lambda (env search-sym)
    (if (empty-env? env)
        (eopl:error 'apply-env "No binding for ~s" search-sym)
        	(let ((sym (extended-env-record->sym env))
                      (val (extended-env-record->val env))
                      (old-env (extended-env-record->old-env env)))
                  (if (eqv? search-sym sym)
                      val
                      (apply-env old-env search-sym))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Expression data type && Program
(define identifier?
  (lambda (exp)
    (and (symbol? exp)
         (not (eqv? exp 'lambda)))))

(define-datatype expression expression?
  (const-exp
   (num number?))
  (if-exp
   (exp1 expression?)
   (exp2 expression?)
   (exp3 expression?))
  (zero?-exp
   (exp1 expression?))
  (var-exp
   (var identifier?))
  (diff-exp
   (exp1 expression?)
   (exp2 expression?))
  (let-exp
   (var  identifier?)
   (exp  expression?)
   (body expression?))
  (proc-exp
   (var identifier?)
   (body expression?))
  (call-exp
   (rator expression?)
   (rand expression?))
  (newref-exp
   (exp1 expression?))
  (deref-exp
   (exp1 expression?))
  (setref-exp
   (exp1 expression?)
   (exp2 expression?))
  (seq-exp
   (exps (list-of expression?)))
  )

(define-datatype program program?
  (a-program (exp1 expression?)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter
(define-datatype answer answer?
  (an-answer
   (val expval?)
   (store store?)))

(define answer->expval
  (lambda (ans)
    (cases answer ans
      (an-answer (val _) val))))


(define answer->store
  (lambda (ans)
    (cases answer ans
      (an-answer (_ store) store))))

;;; I didn't get the idea of code on figure 4.6, page 116
;;; so I wrote my own
(define value-of
  (lambda (exp env store)
    (cases expression exp
      (const-exp (num) (an-answer (num-val num) store))
      (var-exp (var) (an-answer (apply-env env var) store))
      (diff-exp (exp1 exp2)
                (let* ((ans1 (value-of exp1 env store))
                       (val1 (answer->expval ans1))
                       (store1 (answer->store ans1)))
                  (let* ((ans2 (value-of exp2 env store1))
                         (val2 (answer->expval ans2))
                         (store2 (answer->store ans2)))
                    (let ((num1 (expval->num val1))
                          (num2 (expval->num val2)))
                      (an-answer (num-val (- num1 num2))
                                 store2)))))
      (if-exp (exp1 exp2 exp3)
              (let ((ans1 (value-of exp1 env store)))
                (let ((val1 (answer->expval ans1))
                      (store1 (answer->store ans1)))
                (if (expval->bool val1)
                    (value-of exp2 env store1)
                    (value-of exp3 env store1)))))
      (zero?-exp (exp1)
                 (let ((ans1 (value-of exp1 env store)))
                   (let ((val1 (answer->expval ans1))
                         (store1 (answer->store ans1)))
                   (let ((num1 (expval->num val1)))
                     (if (zero? num1)
                         (an-answer (bool-val #t) store1)
                         (an-answer (bool-val #f) store1))))))
      (let-exp (var exp body)
        (let ((ans1  (value-of exp env store)))
          (let ((val1 (answer->expval ans1))
                (store1 (answer->store ans1)))
        
               (value-of body
                         (extend-env var val1 env)
                         store1))))
      (proc-exp (var body)
                (an-answer (proc-val (procedure var body env)) store))
      (call-exp (rator rand)
                (let* ((ans1 (value-of rator env store))
                       (proc (expval->proc (answer->expval ans1)))
                       (store1 (answer->store ans1)))
                  (let* ((ans2 (value-of rand env store1))
                         (arg (answer->expval ans2))
                         (store2 (answer->store ans2)))
                 (apply-procedure proc arg store2))))
      (newref-exp (exp1)
                  (let* ((ans1 (value-of exp1 env store))
                         (val1 (answer->expval ans1))
                         (store1 (answer->store ans1)))
                    (let ((sto&ref (newref val1 store1)))
                      (an-answer (ref-val (cadr sto&ref)) (car sto&ref)))))
  
      (deref-exp (exp1)
                 (let* ((ans1 (value-of exp1 env store))
                        (val1 (answer->expval ans1))
                        (store1 (answer->store ans1)))
                   (let* ((ref1 (expval->ref val1))
                          (sto&val (deref ref1 store1)))
                     (an-answer (cadr sto&val) (car sto&val)))))
      
      (setref-exp (exp1 exp2)
                  (let* ((ans1 (value-of exp1 env store))
                         (val1 (answer->expval ans1))
                         (store1 (answer->store ans1)))
                    (let* ((ans2 (value-of exp2 env store1))
                           (val2 (answer->expval ans2))
                           (store2 (answer->store ans2)))
                      (let ((store3 (car (setref! (expval->ref val1) val2 store2))))
                        (an-answer (num-val 42) store3)))))
      (seq-exp (exps)
               (if (null? exps)
                   (eopl:error 'value-of " empty seq-exp")
                   (let loop ([rest (cdr exps)]
                              [last-ans (value-of (car exps) env store)])
                     (if (null? rest)
                         last-ans
                         (loop (cdr rest) (value-of (car rest) env (answer->store last-ans)))))))
      )))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;run
(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)
    ))

(define the-grammar-spec
  '((program    (expression) a-program)
    (expression (number) const-exp)
    (expression (identifier) var-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    (expression ("(" expression expression ")") call-exp)
    (expression ("newref" "(" expression ")") newref-exp)
    (expression ("deref" "(" expression ")") deref-exp)
    (expression ("setref" "(" expression "," expression ")") setref-exp)
    (expression ("begin"  (separated-list expression ";") "end") seq-exp)
    ))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar-spec))

(define init-env
  (lambda ()
    (extend-env 'true (bool-val #t)
                (extend-env 'false (bool-val #f)
                            (empty-env)))))

; value-of-program : Program → ExpVal
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (value-of exp1 (init-env) (initialize-store!))))))

(define run
  (lambda (string)
    (answer->expval (value-of-program (scan&parse string)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;test
(define str1
  "let x = newref(22)
   in let f = proc (z) let zz = newref(-(z,deref(x)))
                       in deref(zz)
      in -((f 66), (f 55))")
(check-equal? (run str1) (num-val 11))

(define str2
  "let g = let counter = newref(0)
           in proc (dummy)
                begin
                  setref(counter, -(deref(counter), -1));
                  deref(counter)
                end
  in let a = (g 11)
     in let b = (g 11)
        in -(a,b)")
(check-equal? (run str2) (num-val -1))
