mk_new_ann =
  \(ann : Allocation)
   (S : Session)
   (p : < S  >)
   (q : < ~S >)->
  proc()
    new/ ann [c : S, d : ~S]
    ( @p(c)
    | @q(d))
