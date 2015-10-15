par_comm =
 \(A : Session)
  (B : Session)->
 proc(c : {A,B} -o {B,A})
  c{i,o}
  i[na,nb]
  o{b,a}
  (fwd(A)(a,na) | fwd(B)(b,nb))
