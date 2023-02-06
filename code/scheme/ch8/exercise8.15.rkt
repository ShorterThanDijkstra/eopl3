#lang eopl
#|
module tables
  interface
    [opaque table
    empty : table
    add-to-table : (int -> (int -> (table -> table)))
    lookup-in-table : (int -> (table -> int))]
  body
    [type table = (int -> int)
     empty = proc(x: int) -1
     add-to-table = proc(x: int)
                      proc(y: int)
                        proc(saved: table)
                          proc(search: int)
                            if zero?(-(x, search))
                            then y
                            else (saved search)
     lookup-in-table = proc(search: int)
                         proc(t: table)
                           (t search)
    ]
let empty = from tables take empty
in let add-binding = from tables take add-to-table
in let lookup = from tables take lookup-in-table
in let table1 = (((add-binding 3) 300)
                 (((add-binding 4) 400)
                  (((add-binding 3) 600)
                   empty)))
in -(((lookup 4) table1),
((lookup 3) table1))
|#