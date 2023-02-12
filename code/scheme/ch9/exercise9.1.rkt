#lang eopl

(require "CLASSES.rkt")
(require rackunit)

(define ans1
  "
  class queue extends object
    field q
    method initialize() set q = list()
    method empty?() null?(q)
    method enqueue(v) set q = cons(v, q)
    method dequeue()
      if null?(q)
      then false
      else let t = car(q)
               ign = set q = cdr(q)
           in t
  
  let que = new queue()
  in let ign = send que enqueue(3)
  in list(send que empty?(), send que dequeue())" )
(check-equal? (:e ans1)
              (list-val (list (bool-val #f) (num-val 3))))

(define ans2
  "
   class queue extends object
    field q
    method initialize() set q = list()
    method empty?() null?(q)
    method enqueue(v) set q = cons(v, q)
    method dequeue()
      if null?(q)
      then false
      else let t = car(q)
               ign = set q = cdr(q)
           in t
  
  class queue_counter extends queue
    field n
    method initialize() begin super initialize();
                              set n = 0
                        end
    method countup() set n = +(n, 1)
    method get_count() n
    
    method empty?() begin send self countup();
                          super empty?()
                    end
    
    method enqueue(v) begin send self countup();
                            super enqueue(v)
                      end
    method dequeue() begin send self countup();
                           super dequeue()
                     end
  
  let que = new queue_counter()
  in let ign = send que enqueue(3)
  in list(send que empty?(), send que dequeue(), send que get_count())" )

(check-equal? (:e ans2)
              (list-val (list (bool-val #f) (num-val 3) (num-val 3))))

(define ans3
  "
   class counter extends object
     field n
     method initialize() set n = 0
     method countup() set n = +(n, 1)
     method get_count() n
  
   class queue extends object
    field q
    method initialize() set q = list()
    method empty?() null?(q)
    method enqueue(v) set q = cons(v, q)
    method dequeue()
      if null?(q)
      then false
      else let t = car(q)
               ign = set q = cdr(q)
           in t
  
  class queue_counter extends queue
    field n
    field c
    method initialize(a_counter)
      begin super initialize();
            set c = a_counter
      end
    method get_count() send c get_count()
    method empty?() begin send c countup();
                          super empty?()
                    end
    
    method enqueue(v) begin send c countup();
                            super enqueue(v)
                      end
    method dequeue() begin send c countup();
                           super dequeue()
                     end
  let c = new counter()
  in let que1 = new queue_counter(c)
  in let que2 = new queue_counter(c)
  in let ign = send que1 enqueue(3)
  in let ign = send que2 enqueue(7)
  in list(send que1 dequeue(), send que2 dequeue(), send que2 get_count())" )

(check-equal? (:e ans3)
              (list-val (list (num-val 3) (num-val 7) (num-val 4))))