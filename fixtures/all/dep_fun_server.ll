dep_fun_server =
  \(A : Type)
   (B : (x : A)-> Type)
   (f : (x : A)-> B x)->
   proc(c : ?(x : A). !B x)
   recv c (x : A).
   send c (f x)
