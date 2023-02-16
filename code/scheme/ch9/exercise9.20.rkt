#lang eopl
#|
   class c1 extends object
     method initialize() 0
     method m1() 11
     method m2() send this m1()
   class c2 extens c1
     method initialize() 0
     method m1() 21
   let o2 = new c2()
   in send o2 m2()

==>

  class c1 extends object
     method 0() 0
     method 1() 11
     method 2() send this 1()
   class c2 extens c1
     method 3() 0
     method 1() 21
   let o2 = new c2()
   in send o2 m2() % we need type here
|#