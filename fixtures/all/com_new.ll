com_new =
 \(S : Session)
  (p : < S  >)
  (q : < ~S >)->
  proc()
  new(c : S, d : ~S)
  ( @p(c)
  | @q(d))
