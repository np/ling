wrong_order_split_nested_seq :
  (A : Session)(B : Session)(C : Session)(D : Session)->
  < [: A, B, C, D :] -o [: [: A, B :], [: C, D :] :] > =
  \(A : Session)(B : Session)(C : Session)(D : Session)->
   proc(c : {[: ~A, ~B, ~C, ~D :], [: [: A, B :], [: C, D :] :]})
    c{i,o}
    i[:na,nb,nc,nd:]
    o[:ab,cd:]
    ab[:a,b:]
    cd[:c,d:]
    fwd(A)(a,na).
    fwd(C)(c,nc).
    fwd(B)(b,nb).
    fwd(D)(d,nd)
