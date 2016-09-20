rotate_seq = \ (A : Type)(n : Int)->
   proc(i : [: ?A ^(1 + n) :], o : [: !A ^(n + 1) :])
    split i as [:iL, iH^n:]
    split o as [:oL^n, oH:]
    let xL : A <- iL.
    -- TODO: fwd(?A ^ n)(iH, oL).
    sequence ^ n (fwd(?A)(iH, oL)).
    oH <- xL
