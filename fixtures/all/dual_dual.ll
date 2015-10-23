another_dual = \(S : Session)-> ~S
dual_dual =
  \(S : Session)
   (p : < S >)->
   proc(c : ~another_dual S)
   @p(c)
