feed_send =
  \(p : < !Int >)->
  proc()
    new [c : !Int,d].
    ( @p(c) | recv d (x : Int) )
