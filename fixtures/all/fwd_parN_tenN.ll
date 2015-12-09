fwd_parN_tenN = \(n : Int)-> proc(i : {?Int ^ n}, o : [!Int ^ n]) fwd{?Int ^ n}(i,o)

fwd_par10_ten10 = fwd_parN_tenN 10
