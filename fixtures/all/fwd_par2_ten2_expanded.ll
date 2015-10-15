fwd_par2_ten2_expanded =
  proc (i : {?Int, !Int.?Int},o : [!Int, ?Int.!Int])
  o [o0, o1]
  i {i0, i1}
  ( recv i0 (xi0 : Int).
    send o0 xi0
  | recv o1 (xo1 : Int).
    send i1 xo1.
    recv i1 (xi1 : Int).
    send o1 xi1 )
