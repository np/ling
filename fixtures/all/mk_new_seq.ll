mk_new_seq =
  \(ann : Allocation)
   (S : Session)
   (p : <  Log S >)
   (q : < ~Log S >)->
  proc()
    new/ann [: c : Log S, d :]
    @p(c).
    @q(d)
