wrong_fun1_to_proc_ord =
  \(I O : Type)
   (f : (x : I) -> O)->
  proc(c : [: !O, ?I :])
  c[: o, i :]
  recv i (x : I).
  send o (f x)
