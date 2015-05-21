fwd_par2_ten2 (i : {?Int, !Int. ?Int}, o : [!Int, ?Int.!Int])
  = o[o0,o1]
    i{i0,i1}
    ( recv i0 (x : Int) send o0 x
    | recv o1 (x : Int) send i1 x
      recv i1 (x : Int) send o1 x
    ).
