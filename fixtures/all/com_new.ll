com_new =
 \(S : Session)
  (p : < S  >)
  (q : < ~S >)->
  proc()
  new [c : S, d : ~S].
  ( @p(c)
  | @q(d))

com_new_SInt =
  com_new
    (!Int)
    (proc(c' : !Int) c' <- 42)
    (proc(d : ?Int) let x : Int <- d)

com_new_SInt_RBool =
  com_new
    (!Int.?Bool)
    (proc(c' : !Int.?Bool) c' <- 42. let b : Bool <- c')
    (proc(d : ?Int.!Bool) let x : Int <- d. d <- `true)
