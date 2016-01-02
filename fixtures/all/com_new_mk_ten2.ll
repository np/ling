com_new_mk_ten2 =
  let
    mk_tensor2 =
      \ (S0 S1 : Session)
        (p0 : < S0 >)
        (p1 : < S1 >)->
      proc(c : [S0, S1])
        c[c0,c1]
        ( @p0(c0)
        | @p1(c1))
  in
 \(S : Session)
  (p : < S  >)
  (q : < ~S >)->
  proc()
  new [c : S, d : ~S].
  @(mk_tensor2 S (~S) p q)[c,d]

{-
com_new_mk_ten2_SInt =
  com_new_mk_ten2 (!Int) (proc(c' : !Int) send c' 42)
                         (proc(d : ?Int) recv d (x : Int))
-}
