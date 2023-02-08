#lang eopl
#|
module mybool
  interface
    [opaque t
    true : t
    false : t
    and : (t -> (t -> t))
    not : (t -> t)
    to-bool : (t -> bool)]
  body
    [type t = int
     true = 1
     false = 0
     and = proc (x : t)
            proc (y : t)
             if zero?(x) then false else y
    not = proc (x : t)
            if zero?(x) then true else false
    to-bool = proc (x : t)
               if zero?(x) then zero?(1) else zero?(0)]

module mybool-tables
  interface
    [opaque table
    empty : table
    add-to-table : (int ->
                     (from mybool take t ->
                       (table -> table)))
    lookup-in-table : (int ->
                       (table ->
                         from mybool take t))]
  body
    (table-of mybool)

module table-of
  interface
    ((value: [opaque t
              false: t
              true: t
              and : (t -> (t -> t))
              not : (t -> t)
              to-bool : (t -> bool)])
     =>
     [opaque table
      empty: table
      add-to-table: (int -> (from value take t -> (table -> table)))
      lookup-in-table: (int -> (table -> from value take t))])
   body
     module-proc (value: [opaque t
                          false: t
                          true: t
                          and : (t -> (t -> t))
                          not : (t -> t)
                          to-bool : (t -> bool)])
     [type table = (int -> from value take t)
      empty = proc(x: int) from value take false
      add-to-table = proc(x: int)
                      proc(y: from value take t)
                        proc(saved: table)
                          proc(search: int)
                            if zero?(-(x, search))
                            then y
                            else (saved search)
     lookup-in-table = proc(search: int)
                         proc(t: table)
                           (t search)])
      
|#