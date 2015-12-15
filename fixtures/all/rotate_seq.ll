rotate_seq =
  \(A : Type)
   (n : Int)->
   proc(i : [: ?A ^(1 + n) :], o : [: !A ^(n + 1) :])
   i[:iL, iH^n:]
   o[:oL^n, oH:]
   recv iL (xL : A).
   -- TODO: fwd ?A ^ n (iH, oL).
   (slice (iH, oL) n as _
      fwd(?A)(iH, oL)).
   send oH xL

