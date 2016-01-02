feed_send_then_recv =
  \(p : < !Int. ?Int >)
   (f : (x : Int)-> Int)->
  proc()
    new [c : !Int. ?Int,d].
    ( @p(c)
    | recv d (x : Int). send d (f x) )
