wrong_dep_fun_server =
  \(A : Type)
   (B : (x : A)-> Type)
   (y : A)
   (f : (x : A)-> B x)->
   proc(c : ?(x : A). !B x)
   recv c (x : A).
   send c (f y)
