case_fun_server =
  proc(c : ?(x : Bool). (case x of { `true -> !String, `false -> {!String,!String} }))
  recv c (x : Bool).
  @(case x of
    `true -> proc (c) send c "Hello World!"
    `false ->
       proc (c)
       c{d,e}
       send d "Hello".
       send e "World"
  )(c)
