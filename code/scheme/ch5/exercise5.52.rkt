#lang eopl
(require rackunit)
(require racket/format)
(require racket/trace)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Procedure data type
(define-datatype
 proc
 proc?
 (procedure (var identifier?) (body expression?) (saved-env environment?)))
(define apply-procedure/k
  (lambda (proc1 val cont)
    (cases proc
           proc1
           (procedure
            (var body saved-env)
            (value-of/k body (extend-env var (newref val) saved-env) cont)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ExpVal data type
(define-datatype expval
                 expval?
                 (num-val (value number?))
                 (bool-val (boolean boolean?))
                 (proc-val (proc proc?))
                 (pair-val (fst expval?) (snd expval?))
                 (nil-val)
                 (mutex-val (mu mutex?)))

(define show-expval
  (lambda (v)
    (cases expval
           v
           (num-val (num) (~a num))
           (bool-val (bool) (~a bool))
           (proc-val (proc) "<procedure>")
           (pair-val (fst snd) (~a "[" (show-pairs (pair-val fst snd)) "]"))
           (nil-val () "nil")
           (mutex-val (mu) "mutex"))))

(define show-pairs
  (lambda (p)
    (cases expval
           p
           (pair-val (fst snd)
                     (if (nil? snd)
                         (show-expval fst)
                         (~a (show-expval fst) "," (show-pairs snd))))
           (else (eopl:error 'show-pairs)))))

(define expval->num
  (lambda (v)
    (cases expval
           v
           (num-val (num) num)
           (else (eopl:error 'expval->num "~s" v)))))

(define expval->mutex
  (lambda (v)
    (cases expval
           v
           (mutex-val (mu) mu)
           (else (eopl:error 'expval->mutex "~s" v)))))

(define expval->bool
  (lambda (v)
    (cases expval
           v
           (bool-val (bool) bool)
           (else (eopl:error 'expval->bool "~s" v)))))

(define expval->proc
  (lambda (v)
    (cases expval
           v
           (proc-val (proc) proc)
           (else (eopl:error 'expval->proc "~s" v)))))

(define expval->pair-fst
  (lambda (v)
    (cases expval
           v
           (pair-val (fst snd) fst)
           (else (eopl:error 'expval->pair-fst)))))

(define expval->pair-snd
  (lambda (v)
    (cases expval
           v
           (pair-val (fst snd) snd)
           (else (eopl:error 'expval->pair-snd)))))

(define expval->nil
  (lambda (v)
    (cases expval v (nil-val () 'nil) (else (eopl:error 'expval->nil)))))

(define nil? (lambda (v) (cases expval v (nil-val () #t) (else #f))))

(define pair-val?
  (lambda (v) (cases expval v (pair-val (fst snd) #t) (else #f))))

(define list->pair-vals
  (lambda (lst)
    (if (null? lst)
        (nil-val)
        (pair-val (car lst) (list->pair-vals (cdr lst))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Store
(define empty-store (lambda () '()))

(define the-store 'uninitialized)

(define get-store (lambda () the-store))

(define initialize-store! (lambda () (set! the-store (empty-store))))

(define reference? (lambda (v) (integer? v)))

(define newref
  (lambda (val)
    (let ([next-ref (length the-store)])
      (set! the-store (append the-store (list val)))
      next-ref)))

(define deref (lambda (ref) (list-ref the-store ref)))

(define setref!
  (lambda (ref val)
    (set!
     the-store
     (letrec ([setref-inner
               (lambda (store1 ref1)
                 (cond
                   [(null? store1)
                    (eopl:error "report-invalid-reference ~s" ref the-store)]
                   [(zero? ref1) (cons val (cdr store1))]
                   [else
                    (cons (car store1)
                          (setref-inner (cdr store1) (- ref1 1)))]))])
       (setref-inner the-store ref)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Mutex
(define-datatype mutex
                 mutex?
                 (a-mutex (ref-to-closed? reference?)
                          (ref-to-wait-queue reference?)))

(define new-mutex (lambda () (a-mutex (newref #f) (newref '()))))

; wait-for-mutex : Mutex × Thread → FinalAnswer
; usage: waits for mutex to be open, then closes it.
(define wait-for-mutex
  (lambda (m th)
    (cases mutex
           m
           (a-mutex (ref-to-closed? ref-to-wait-queue)
                    (cond
                      [(deref ref-to-closed?)
                       (setref! ref-to-wait-queue
                                (enqueue (deref ref-to-wait-queue) th))
                       (run-next-thread)]
                      [else
                       (setref! ref-to-closed? #t)
                       (th)])))))

; signal-mutex : Mutex × Thread → FinalAnswer
(define signal-mutex
  (lambda (m th)
    (cases mutex
           m
           (a-mutex
            (ref-to-closed? ref-to-wait-queue)
            (let ([closed? (deref ref-to-closed?)]
                  [wait-queue (deref ref-to-wait-queue)])
              (when closed?
                (if (empty? wait-queue)
                    (setref! ref-to-closed? #f)
                    (dequeue wait-queue
                             (lambda (first-waiting-th other-waiting-ths)
                               (place-on-ready-queue! first-waiting-th)
                               (setref! ref-to-wait-queue other-waiting-ths)))))
              (th))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Env
(define-datatype
 environment
 environment?
 (empty-env)
 (extend-env (var identifier?) (ref reference?) (env environment?))
 (extend-env-rec (p-name identifier?)
                 (b-var identifier?)
                 (body expression?)
                 (env environment?)))

(define apply-env
  (lambda (env search-var)
    (cases environment
           env
           (empty-env () (eopl:error 'apply-env "No binding for ~s" search-var))
           (extend-env
            (bvar ref saved-env)
            (if (eqv? search-var bvar) ref (apply-env saved-env search-var)))
           (extend-env-rec (p-name b-var p-body saved-env)
                           (if (eqv? search-var p-name)
                               (newref (proc-val (procedure b-var p-body env)))
                               (apply-env saved-env search-var))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Expression && Parsing
(define-datatype program program? (a-program (expr expression?)))

(define identifier? (lambda (exp) (and (symbol? exp) (not (eqv? exp 'lambda)))))

(define-datatype
 expression
 expression?
 (const-exp (num number?))
 (if-exp (exp1 expression?) (exp2 expression?) (exp3 expression?))
 (zero?-exp (exp1 expression?))
 (var-exp (var identifier?))
 (assign-exp (var identifier?) (exp1 expression?))
 (diff-exp (exp1 expression?) (exp2 expression?))
 (let-exp (var identifier?) (exp expression?) (body expression?))
 (letrec-exp (p-name identifier?)
             (b-var identifier?)
             (p-body expression?)
             (letrec-body expression?))
 (proc-exp (var identifier?) (body expression?))
 (call-exp (rator expression?) (rand expression?))
 (seq-exp (fst expression?) (exps (list-of expression?)))
 (spawn-exp (exp1 expression?))
 (print-exp (exp1 expression?))
 (cons-exp (fst-exp expression?) (snd-exp expression?))
 (car-exp (pair-exp expression?))
 (cdr-exp (pair-exp expression?))
 (null?-exp (exp expression?))
 (nil-exp)
 (list-exp (exps (list-of expression?)))
 (mutex-exp)
 (wait-exp (exp1 expression?))
 (signal-exp (exp1 expression?)))

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define the-grammar-spec
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression (identifier) var-exp)
    (expression ("set" identifier "=" expression) assign-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression
     ("letrec" identifier "(" identifier ")" "=" expression "in" expression)
     letrec-exp)
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    (expression ("(" expression expression ")") call-exp)
    (expression ("begin" expression ";" (separated-list expression ";") "end")
                seq-exp)
    (expression ("spawn" "(" expression ")") spawn-exp)
    (expression ("print" "(" expression ")") print-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("null?" "(" expression ")") null?-exp)
    (expression ("nil") nil-exp)
    (expression ("[" (separated-list expression ",") "]") list-exp)
    (expression ("mutex" "(" ")") mutex-exp)
    (expression ("wait" "(" expression ")") wait-exp)
    (expression ("signal" "(" expression ")") signal-exp)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar-spec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Scheduler
(define empty-queue (lambda () '()))

(define empty? null?)

(define enqueue (lambda (queue th) (append queue (list th))))

(define dequeue (lambda (queue f) (f (car queue) (cdr queue))))

(define the-ready-queue 'uninitialized)
(define the-final-answer 'uninitialized)
(define the-max-time-slice 'uninitialized)
(define the-time-remaining 'uninitialized)

; initialize-scheduler! : Int → Unspecified
(define initialize-scheduler!
  (lambda (ticks)
    (set! the-ready-queue (empty-queue))
    (set! the-final-answer 'uninitialized)
    (set! the-max-time-slice ticks)
    (set! the-time-remaining the-max-time-slice)))

; place-on-ready-queue! : Thread → Unspecified
(define place-on-ready-queue!
  (lambda (th) (set! the-ready-queue (enqueue the-ready-queue th))))
; run-next-thread : () → FinalAnswer
(define run-next-thread
  (lambda ()
    (if (empty? the-ready-queue)
        the-final-answer
        (dequeue the-ready-queue
                 (lambda (first-ready-thread other-ready-threads)
                   (set! the-ready-queue other-ready-threads)
                   (set! the-time-remaining the-max-time-slice)
                   (first-ready-thread))))))
; set-final-answer! : ExpVal → Unspecified
(define set-final-answer! (lambda (val) (set! the-final-answer val)))
; time-expired? : () → Bool
(define time-expired? (lambda () (zero? the-time-remaining)))
; decrement-timer! : () → Unspecified
(define decrement-timer!
  (lambda () (set! the-time-remaining (- the-time-remaining 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;Continuation
(define-datatype
 continuation
 continuation?
 (end-main-thread-cont)
 (end-subthread-cont)
 (zero1-cont (cont continuation?))
 (let-exp-cont (var identifier?)
               (body expression?)
               (env environment?)
               (saved-cont continuation?))
 (if-test-cont (exp2 expression?)
               (exp3 expression?)
               (env environment?)
               (saved-cont continuation?))
 (diff1-cont (exp2 expression?) (env environment?) (saved-cont continuation?))
 (diff2-cont (val1 expval?) (saved-cont continuation?))
 (rator-cont (rand expression?) (env environment?) (saved-cont continuation?))
 (rand-cont (val1 expval?) (saved-cont continuation?))
 (set-rhs-cont (var identifier?) (env environment?) (saved-cont continuation?))
 (seq-cont (exps (list-of expression?))
           (env environment?)
           (saved-cont continuation?))
 (spawn-cont (saved-cont continuation?))
 (print-cont (saved-cont continuation?))
 (cons-fst-cont (snd-exp expression?)
                (env environment?)
                (saved-cont continuation?))
 (cons-snd-cont (val1 expval?) (saved-cont continuation?))
 (car-cont (saved-cont continuation?))
 (cdr-cont (saved-cont continuation?))
 (null?-cont (saved-cont continuation?))
 (list-cont (exps (list-of expression?))
            (vals (list-of expval?))
            (env environment?)
            (saved-cont continuation?))
 (wait-cont (saved-cont continuation?))
 (signal-cont (saved-cont continuation?)))

(define apply-cont
  (lambda (cont val)
    (if (time-expired?)
        (begin
          (place-on-ready-queue! (lambda () (apply-cont cont val)))
          (run-next-thread))
        (begin
          (decrement-timer!)
          (cases
           continuation
           cont
           (zero1-cont
            (saved-cont)
            (apply-cont saved-cont (bool-val (zero? (expval->num val)))))
           (let-exp-cont (var body saved-env saved-cont)
                         (value-of/k body
                                     (extend-env var (newref val) saved-env)
                                     saved-cont))
           (if-test-cont (exp2 exp3 saved-env saved-cont)
                         (if (expval->bool val)
                             (value-of/k exp2 saved-env saved-cont)
                             (value-of/k exp3 saved-env saved-cont)))
           (diff1-cont (exp2 env saved-cont)
                       (value-of/k exp2 env (diff2-cont val saved-cont)))
           (diff2-cont (val1 saved-cont)
                       (let ([num1 (expval->num val1)] [num2 (expval->num val)])
                         (apply-cont saved-cont (num-val (- num1 num2)))))
           (rator-cont (rand env saved-cont)
                       (value-of/k rand env (rand-cont val saved-cont)))
           (rand-cont (val1 saved-cont)
                      (let ([proc1 (expval->proc val1)])
                        (apply-procedure/k proc1 val saved-cont)))
           (set-rhs-cont (var env saved-cont)
                         (begin
                           (setref! (apply-env env var) val)
                           (apply-cont saved-cont val)))
           (seq-cont (exps env saved-cont)
                     (if (null? exps)
                         (apply-cont saved-cont val)
                         (value-of/k (car exps)
                                     env
                                     (seq-cont (cdr exps) env saved-cont))))
           (spawn-cont
            (saved-cont)
            (let ([proc1 (expval->proc val)])
              (place-on-ready-queue!
               (lambda ()
                 (apply-procedure/k proc1 (num-val 28) (end-subthread-cont))))
              (apply-cont saved-cont (num-val 73))))
           (end-main-thread-cont () (set-final-answer! val) (run-next-thread))
           (end-subthread-cont () (run-next-thread))
           (print-cont (saved-cont)
                       (display (show-expval val))
                       (newline)
                       (apply-cont saved-cont (num-val 73)))
           (cons-fst-cont (snd-exp env cont)
                          (value-of/k snd-exp env (cons-snd-cont val cont)))
           (cons-snd-cont (val1 cont) (apply-cont cont (pair-val val1 val)))
           (car-cont (cont)
                     (let ([fst (expval->pair-fst val)]) (apply-cont cont fst)))
           (cdr-cont (cont)
                     (let ([fst (expval->pair-snd val)]) (apply-cont cont fst)))
           (null?-cont (cont) (apply-cont cont (bool-val (nil? val))))
           (list-cont
            (exps vals env cont)
            (if (null? exps)
                (apply-cont cont (list->pair-vals (reverse (cons val vals))))
                (value-of/k (car exps)
                            env
                            (list-cont (cdr exps) (cons val vals) env cont))))
           (wait-cont (saved-cont)
                      (wait-for-mutex
                       (expval->mutex val)
                       (lambda () (apply-cont saved-cont (num-val 52)))))
           (signal-cont (saved-cont)
                        (signal-mutex
                         (expval->mutex val)
                         (lambda () (apply-cont saved-cont (num-val 53))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter
(define init-env
  (lambda ()
    (extend-env 'true
                (newref (bool-val #t))
                (extend-env 'false (newref (bool-val #f)) (empty-env)))))

(define value-of-program
  (lambda (timeslice pgm)
    (initialize-store!)
    (initialize-scheduler! timeslice)
    (cases program
           pgm
           (a-program (exp1)
                      (value-of/k exp1 (init-env) (end-main-thread-cont))))))

(define value-of/k
  (lambda (exp env cont)
    (cases
     expression
     exp
     (const-exp (num) (apply-cont cont (num-val num)))
     (var-exp (var) (apply-cont cont (deref (apply-env env var))))
     (assign-exp (var exp1) (value-of/k exp1 env (set-rhs-cont var env cont)))
     (proc-exp (var body) (apply-cont cont (proc-val (procedure var body env))))
     (letrec-exp
      (p-name b-var p-body letrec-body)
      (value-of/k letrec-body (extend-env-rec p-name b-var p-body env) cont))
     (zero?-exp (exp1) (value-of/k exp1 env (zero1-cont cont)))
     (if-exp (exp1 exp2 exp3)
             (value-of/k exp1 env (if-test-cont exp2 exp3 env cont)))
     (let-exp (var exp1 body)
              (value-of/k exp1 env (let-exp-cont var body env cont)))
     (diff-exp (exp1 exp2) (value-of/k exp1 env (diff1-cont exp2 env cont)))
     (call-exp (rator rand) (value-of/k rator env (rator-cont rand env cont)))
     (seq-exp (fst exps) (value-of/k fst env (seq-cont exps env cont)))
     (spawn-exp (exp1) (value-of/k exp1 env (spawn-cont cont)))
     (print-exp (exp1) (value-of/k exp1 env (print-cont cont)))
     (cons-exp (fst-exp snd-exp)
               (value-of/k fst-exp env (cons-fst-cont snd-exp env cont)))
     (car-exp (pair-exp) (value-of/k pair-exp env (car-cont cont)))
     (cdr-exp (pair-exp) (value-of/k pair-exp env (cdr-cont cont)))
     (null?-exp (expr) (value-of/k expr env (null?-cont cont)))
     (nil-exp () (apply-cont cont (nil-val)))
     (list-exp
      (exps)
      (if (null? exps)
          (apply-cont cont (nil-val))
          (value-of/k (car exps) env (list-cont (cdr exps) (list) env cont))))
     (mutex-exp () (apply-cont cont (mutex-val (new-mutex))))
     (wait-exp (exp1) (value-of/k exp1 env (wait-cont cont)))
     (signal-exp (exp1) (value-of/k exp1 env (signal-cont cont))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; run
(define run (lambda (code) (value-of-program 5 (scan&parse code))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; (trace value-of/k)
;;; test
(define str0
  "
  letrec double(x) = if zero?(x) then 0 else -((double -(x,1)), -2)
  in (double 6)
   ")
(check-equal? (run str0) (num-val 12))

(define str1 "
  letrec id(x) = x
  in (id 0)
   ")
(check-equal? (run str1) (num-val 0))

(define str2
  "let g = let counter = 0
           in proc (dummy)
                begin
                  set counter = -(counter, -1);
                  counter
                end
  in let a = (g 11)
     in let b = (g 11)
        in -(a,b)")
(check-equal? (run str2) (num-val -1))

(define str4
  "let f = proc (x) proc (y)
            begin
              set x = -(x,-1);
              -(x,y)
            end
  in ((f 44) 33)")
(check-equal? (run str4) (num-val 12))

(define str5
  "let p = proc (x) set x = 4
   in let a = 3
   in begin (p a); a end")
(check-equal? (run str5) (num-val 3))

(define str6 "let p = 114
   in let void = set p = -(514, p)
      in p
  ")
(check-equal? (run str6) (num-val 400))

(define str7
  "let x = 0
   in let inc1 = proc(x) -(x, -1)
      in let incr_x = proc (id)
                       proc (dummy)
                         begin
                            set x = (inc1 x);
                            print(x)
                         end
          in begin
               spawn((incr_x 100));
               spawn((incr_x 200));
               spawn((incr_x 300));
               x
          end")
(run str7)

(define str8
  "letrec
   noisy (l) = if null?(l)
               then 0
               else begin print(car(l)); (noisy cdr(l)) end
   in
   begin
     spawn(proc (d) (noisy [1,2,3,4,5])) ;
     spawn(proc (d) (noisy [6,7,8,9,10])) ;
     print(100);
     33
   end")
(check-equal? (run str8) (num-val 33))

(define str9
  "let buffer = 0
   in let producer = proc (n)
                       letrec waits(k) = if zero?(k)
                                        then set buffer = n
                                        else begin
                                               print(-(k,-200));
                                               (waits -(k,1))
                                             end
                       in (waits 5)
   in let consumer = proc (d)
                       letrec busywait (k) = if zero?(buffer)
                                             then begin
                                                    print(-(k,-100));
                                                    (busywait -(k,-1))
                                                  end
                                             else buffer
                       in (busywait 0)
   in begin
        spawn(proc (d) (producer 44));
        print(300);
        (consumer 86)
   end")
(check-equal? (run str9) (num-val 44))

(define str10
  "let x = 0
   in let inc1 = proc(x) -(x, -1)
      in let mut = mutex()
         in let incr_x = proc (id)
                           proc (dummy)
                             begin
                               wait(mut);
                               set x = (inc1 x);
                               print(x);
                               signal(mut)
                             end
            in begin
                 spawn((incr_x 100));
                 spawn((incr_x 200));
                 spawn((incr_x 300));
                 x
            end")
(run str10)



(define str11
  "let x = 0
   in let inc1 = proc(x) -(x, -1)
      in let mut = mutex()
         in let incr_x = proc (id)
                           proc (dummy)
                               set x = (inc1 x)
            in begin
                 wait(mut);
                 spawn((incr_x 100));
                 signal(mut);
  
                 wait(mut);
                 spawn((incr_x 200));
                 signal(mut);
  
                 wait(mut);
                 spawn((incr_x 300));
                 signal(mut);
  
                 x
            end")
(run str11)