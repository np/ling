wrong_plug_send_recv =
  \(p : < !Int, ?Int >)->
  proc(c : !Int, d : ?Int)
    @p(d,c)
