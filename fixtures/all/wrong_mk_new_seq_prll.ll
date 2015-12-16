wrong_mk_new_seq_prll =
  \(ann : Allocation)
   (S : Session)
   (p : <  Log S >)
   (q : < ~Log S >)->
  proc()
    new/ann [: c : Log S, d :]
    ( @p(c)
    | @q(d))
