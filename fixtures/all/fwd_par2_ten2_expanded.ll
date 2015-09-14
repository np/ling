fwd_par2_ten2_expanded (i : {?Int, !Int. ?Int}, o : [!Int, ?Int.!Int])
  = o[o0,o1]
    i{i0,i1}
    ( recv i0 (xi0 : Int) send o0 xi0
    | recv o1 (xo1 : Int) send i1 xo1
      recv i1 (yi1 : Int) send o1 yi1
    ).
