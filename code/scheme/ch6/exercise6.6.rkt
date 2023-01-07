#lang eopl
#|
(lambda (x y) (+ (f (g x)) (h (j y))))

g j f h +
j g f h +
j g h f +
g j h f +
g f j h +
j h g f +
|#

