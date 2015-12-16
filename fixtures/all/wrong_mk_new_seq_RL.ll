wrong_mk_new_seq_RL =
  \(ann : Allocation)
   (S : Session)
   (p : <  Log S >)
   (q : < ~Log S >)->
  proc()
    new/ann [: c : Log S, d :]
    @q(d).
    @p(c)
