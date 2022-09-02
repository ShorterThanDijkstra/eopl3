#lang eopl
#|
1.  top-down:
    A natural number x is in S if and only if
    (1) x = 2, or
    (2) x - 3 in S

    bottom-up:
    Define the set S to be the smallest set contained in N and satisfying the following properties
    (1) 2 in S, and
    (2) if x in S, then x + 3 in S

    rules of inference:
                   x in S
    ------      -------------
    2 in S       (x + 3) in S


2.  top-down:
    A natural number x is in S if and only if
    (1) x = 1, or
    (2) x - 3 in S, or
    (3) x - 2 in S

    bottom-up:
    Define the set S to be the smallest set contained in N and satisfying the following properties
    (1) 1 in S, and
    (2) if x in S, then x + 2 in S, and
    (3) if x in S, then x + 3 in S

    rules of inference:
                   x in S               x in S
    ------      -------------        -------------
    1 in S       (x + 2) in S         (x + 3) in S


3.  top-down:
    A pair of natural numbers (x, y) is in S if and only if
    (1) (x, y) = (0, 1), or
    (2) (x - 1, y - 2) in S

    bottom-up:
    Define the set S to be the smallest set of pair of natural numbers and satisfying the following properties
    (1) (0, 1) in S, and
    (2) if (x, y) in S, then (x + 1, y + 2) in S


    rules of inference:
                          (x, y) in S              
    -----------      --------------------      
    (0, 1) in S       (x + 1, y + 2) in S        


4.  top-down:
    A pair of natural numbers (x, y) is in S if and only if
    (1) (x, y) = (0, 0), or
    (2) (x - 1, y - 2x + 1) in S

    bottom-up:
    Define the set S to be the smallest set of pair of natural numbers and satisfying the following properties
    (1) (0, 0) in S, and
    (2) if (x, y) in S, then (x + 1, y + 2x + 1) in S


    rules of inference:
                           (x, y) in S              
    -----------      -------------------------    
    (0, 0) in S       (x + 1, y + 2x + 1) in S   
|#