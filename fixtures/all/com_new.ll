com_new =
 \(S : Session)
  (p : < S  >)
  (q : < ~S >)->
  proc()
  new(c : S, d : ~S)
  ( @p(c)
  | @q(d))

com_new_SInt =
  com_new
    (!Int)
    (proc(c' : !Int) send c' 42)
    (proc(d : ?Int) recv d (x : Int))
