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
  (lambda ()
    (cases proc
      _proc1_
      (procedure
       (var body saved-env)
       (begin
         (set! _exp_ body)
         (set! _env_ (extend-env var (newref _val_) saved-env))
         (set! _cont_ _cont_)
         (value-of/k))))))

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
  (lambda ()
    (if (time-expired?)
        (begin
        ;  一旦使用全局变量和set!，就要注意闭包的使用
          (place-on-ready-queue! (let ((saved-cont _cont_)
                                       (saved-val _val_))
                                   (lambda () (begin (set! _cont_ saved-cont)
                                                   (set! _val_ saved-val)
                                                   (apply-cont)))))
          (run-next-thread))
        (begin
          (decrement-timer!)
          (cases
              continuation
            _cont_
            (zero1-cont
             (saved-cont)
             (set! _cont_ saved-cont)
             (set! _val_ (bool-val (zero? (expval->num _val_))))
             (apply-cont))
            (let-exp-cont (var body saved-env saved-cont)
                          (set! _exp_ body)
                          (set! _env_ (extend-env var (newref _val_) saved-env))
                          (set! _cont_ saved-cont)
                          (value-of/k))
            (if-test-cont (exp2 exp3 saved-env saved-cont)
                          (set! _exp_ (if (expval->bool _val_) exp2 exp3))
                          (set! _env_ saved-env)
                          (set! _cont_ saved-cont)
                          (value-of/k))
            (diff1-cont (exp2 env saved-cont)
                        (set! _exp_ exp2)
                        (set! _cont_ (diff2-cont _val_ saved-cont))
                        (set! _env_ _env_)
                        (value-of/k))
            (diff2-cont (val1 saved-cont)
                        (let ([num1 (expval->num val1)] [num2 (expval->num _val_)])
                          (set! _cont_ saved-cont)
                          (set! _val_ (num-val (- num1 num2)))
                          (apply-cont)))
            (rator-cont (rand env saved-cont)
                        (set! _exp_ rand)
                        (set! _env_ _env_)
                        (set! _cont_ (rand-cont _val_ saved-cont))
                        (value-of/k))
            (rand-cont (val1 saved-cont)
                       (let ([proc1 (expval->proc val1)])
                         (set! _proc1_ proc1)
                         (set! _val_ _val_)
                         (set! _cont_ saved-cont)
                         (apply-procedure/k)))
            (set-rhs-cont (var env saved-cont)
                          (begin
                            (setref! (apply-env env var) _val_)
                            (set! _cont_ saved-cont)
                            (set! _val_ _val_)
                            (apply-cont)))
            (seq-cont (exps saved-env saved-cont)
                      (if (null? exps)
                          (begin (set! _cont_ saved-cont)
                                 (set! _val_ _val_)
                                 (apply-cont))
                          (begin (set! _exp_  (car exps))
                                 (set! _env_ saved-env)
                                 (set! _cont_ (seq-cont (cdr exps) _env_ saved-cont))
                                 (value-of/k))))
            (spawn-cont
             (saved-cont)
             (let ([proc1 (expval->proc _val_)])
               (begin (place-on-ready-queue!
                       (lambda ()
                         (begin (set! _proc1_ proc1)
                                (set! _val_ (num-val 28))
                                (set! _cont_  (end-subthread-cont))
                                (apply-procedure/k))))
                      (set! _cont_ saved-cont)
                      (set! _val_ (num-val 73))
                      (apply-cont))))
            (end-main-thread-cont ()
                                  (set-final-answer! _val_) (run-next-thread))
            (end-subthread-cont () (run-next-thread))
            (print-cont (saved-cont)
                        (display (show-expval _val_))
                        (newline)
                        (set! _cont_ saved-cont)
                        (set! _val_  (num-val 73))
                        (apply-cont))
            (cons-fst-cont (snd-exp env cont)
                           (set! _exp_ snd-exp)
                           (set! _cont_ (cons-snd-cont _val_ cont))
                           (set! _env_ _env_)
                           (value-of/k))
            (cons-snd-cont (val1 saved-cont)
                           (set! _cont_ saved-cont)
                           (set! _val_ (pair-val val1 _val_))
                           (apply-cont))
            (car-cont (saved-cont)
                      (let ([fst (expval->pair-fst _val_)])
                        (set! _cont_ saved-cont)
                        (set! _val_ fst)
                        (apply-cont)))
            (cdr-cont (saved-cont)
                      (let ([snd (expval->pair-snd _val_)])
                        (set! _cont_ saved-cont)
                        (set! _val_ snd)
                        (apply-cont)))
            (null?-cont (saved-cont)
                        (set! _cont_ saved-cont)
                        (set! _val_ (bool-val (nil? _val_)))
                        (apply-cont))
            (list-cont
             (exps vals env saved-cont)
             (if (null? exps)
                 (begin (set! _cont_ saved-cont)
                        (set! _val_ (list->pair-vals (reverse (cons _val_ vals))))
                        (apply-cont))
                 (begin (set! _exp_  (car exps))
                        (set! _cont_ (list-cont (cdr exps) (cons _val_ vals) env saved-cont))
                        (set! _env_ env)
                        (value-of/k))))
            (wait-cont (saved-cont)
                       (wait-for-mutex
                        (expval->mutex _val_)
                        (lambda ()
                          (begin (set! _cont_ saved-cont)
                                 (set! _val_ (num-val 52))
                                 (apply-cont)))))
            (signal-cont (saved-cont)
                         (signal-mutex
                          (expval->mutex _val_)
                          (lambda ()
                            (begin (set! _cont_ saved-cont)
                                   (set! _val_ (num-val 53))
                                   (apply-cont))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interpreter
(define init-env
  (lambda ()
    (extend-env 'true
                (newref (bool-val #t))
                (extend-env 'false (newref (bool-val #f)) (empty-env)))))

(define _exp_ 'uninitialized)
(define _env_ 'uninitialized)
(define _cont_ 'uninitialized)
(define _val_ 'uninitialized)
(define _proc1_ 'uninitialized)

(define value-of-program
  (lambda (timeslice pgm)
    (initialize-store!)
    (initialize-scheduler! timeslice)
    (cases program
      pgm
      (a-program (exp1)
                 (set! _exp_ exp1)
                 (set! _env_ (init-env))
                 (set! _cont_ (end-main-thread-cont))
                 (value-of/k)))))

(define value-of/k
  (lambda ()
    (cases
        expression
      _exp_
      (const-exp (num)
                 (set! _cont_ _cont_)
                 (set! _val_ (num-val num))
                 (apply-cont))
      (var-exp (var)
               (set! _cont_ _cont_)
               (set! _val_ (deref (apply-env _env_ var)))
               (apply-cont))
      (assign-exp (var exp1)
                  (set! _exp_ exp1)
                  (set! _cont_ (set-rhs-cont var _env_ _cont_))
                  (value-of/k))
      (proc-exp (var body)
                (set! _cont_ _cont_)
                (set! _val_  (proc-val (procedure var body _env_)))
                (apply-cont))
      (letrec-exp
       (p-name b-var p-body letrec-body)
       (set! _exp_ letrec-body)
       (set! _env_ (extend-env-rec p-name b-var p-body _env_))
       (set! _cont_ _cont_)
       (value-of/k))
      (zero?-exp (exp1)
                 (set! _exp_ exp1)
                 (set! _env_ _env_)
                 (set! _cont_ (zero1-cont _cont_))
                 (value-of/k))
      (if-exp (exp1 exp2 exp3)
              (set! _exp_ exp1)
              (set! _env_ _env_)
              (set! _cont_  (if-test-cont exp2 exp3 _env_ _cont_))
              (value-of/k))
      (let-exp (var exp1 body)
               (set! _exp_ exp1)
               (set! _cont_ (let-exp-cont var body _env_ _cont_))
               (set! _env_ _env_)
               (value-of/k))
      (diff-exp (exp1 exp2)
                (set! _exp_ exp1)
                (set! _cont_ (diff1-cont exp2 _env_ _cont_))
                (set! _env_ _env_)
                (value-of/k))
      (call-exp (rator rand)
                (set! _exp_ rator)
                (set! _cont_ (rator-cont rand _env_ _cont_))
                (set! _env_ _env_)
                (value-of/k))
      (seq-exp (fst exps)
               (set! _exp_ fst)
               (set! _cont_ (seq-cont exps _env_ _cont_))
               (set! _env_ _env_)
               (value-of/k))
      (spawn-exp (exp1)
                 (set! _exp_ exp1)
                 (set! _cont_ (spawn-cont _cont_))
                 (set! _env_ _env_)
                 (value-of/k))
      (print-exp (exp1)
                 (set! _exp_ exp1)
                 (set! _env_ _env_)
                 (set! _cont_  (print-cont _cont_))
                 (value-of/k))
      (cons-exp (fst-exp snd-exp)
                (set! _exp_ fst-exp)
                (set! _cont_ (cons-fst-cont snd-exp _env_ _cont_))
                (set! _env_ _env_)
                (value-of/k))
      (car-exp (pair-exp)
               (set! _exp_ pair-exp)
               (set! _cont_ (car-cont _cont_))
               (set! _env_ _env_)
               (value-of/k))
      (cdr-exp (pair-exp)
               (set! _exp_ pair-exp)
               (set! _env_ _env_)
               (set! _cont_ (cdr-cont _cont_))
               (value-of/k))
      (null?-exp (expr)
                 (set! _exp_ expr)
                 (set! _env_ _env_)
                 (set! _cont_ (null?-cont _cont_))
                 (value-of/k))
      (nil-exp ()
               (set! _cont_ _cont_)
               (set! _val_ (nil-val))
               (apply-cont ))
      (list-exp
       (exps)
       (if (null? exps)
           (begin (set! _cont_ _cont_)
                  (set! _val_ (nil-val))
                  (apply-cont))
           (begin (set! _exp_ (car exps))
                  (set! _cont_ (list-cont (cdr exps) (list) _env_ _cont_))
                  (set! _env_ _env_)
                  (value-of/k))))
      (mutex-exp ()
                 (set! _cont_ _cont_)
                 (set! _val_ (mutex-val (new-mutex)))
                 (apply-cont))
      (wait-exp (exp1)
                (set! _exp_ exp1)
                (set! _cont_ (wait-cont _cont_))
                (set! _env_ _env_)
                (value-of/k))
      (signal-exp (exp1)
                  (set! _exp_ exp1)
                  (set! _env_ _env_)
                  (set! _cont_ (signal-cont _cont_))
                  (value-of/k)))))

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
