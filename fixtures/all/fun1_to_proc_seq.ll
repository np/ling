fun1_to_proc_seq =
  \(I : Type)
   (O : Type)
   (f : (x : I) -> O)->
  proc(c : ?I. !O)
  recv c (x : I).
  send c (f x)
