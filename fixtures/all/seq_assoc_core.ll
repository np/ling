seq_assoc_core =
 \(A : Session)
  (B : Session)
  (C : Session)->
 proc(i : ~[:[:A,B:],C:], o : [:A,[:B,C:]:])
  i[:nab,nc:]
  nab[:na,nb:]
  o[:a,bc:]
  bc[:b,c:]
  fwd(A)(a,na). fwd(B)(b,nb). fwd(C)(c,nc)
