feed_recv =
  \(p : < ?Int >)
   (i : Int)->
  proc()
    new [c : ?Int,d].
    ( @p(c) | send d i )
