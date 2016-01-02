wrong_feed_send_with_send =
  \(p : < !Int >)->
  proc()
    new [c : !Int,d].
    ( @p(c) | send d 4 )
