-- a needlessly complicated version of mk_tensor2
-- (should be convertible with it)
mk_ten2_2new_2fwd =
 \(S0 S1 : Session)
  (p0 : < S0 >)
  (p1 : < S1 >)->
  proc(c : [S0, S1])
  c[c0,c1]
  new [d0 : ~S0, e0 : S0].
  new [d1 : ~S1, e1 : S1].
  ( @p0(e0)
  | fwd S0 (c0, d0)
  | @p1(e1)
  | fwd S1 (c1, d1))

{-
mk_ten2_2new_2fwd_SInt_SDouble =
  let mk_send = \(A : Type)(x : A)-> proc(c : !A) send c x in
  mk_ten2_2new_2fwd (!Int) (!Double)
    (mk_send Int 42) (mk_send Double 3.14)

mk_ten2_2new_2fwd_SInt_SDouble =
  mk_ten2_2new_2fwd (!Int) (!Double)
    (proc(ci : !Int) send ci 42) (proc(cd : !Double) send cd 3.14)
-}
