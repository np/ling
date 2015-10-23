split_nested_seq_core =
  \(A : Session)(B : Session)(C : Session)(D : Session)->
   proc(i : [: ~A, ~B, ~C, ~D :], o : [: [: A, B :], [: C, D :] :])
    i[:na,nb,nc,nd:]
    o[:ab,cd:]
    ab[:a,b:]
    cd[:c,d:]
    fwd A (a,na).
    fwd B (b,nb).
    fwd C (c,nc).
    fwd D (d,nd)

group_nested_seq :
  (A : Session)(B : Session)(C : Session)(D : Session)->
  < [: [: A, B :], [: C, D :] :] -o [: A, B, C, D :] > =
  \(A : Session)(B : Session)(C : Session)(D : Session)->
   proc(c : {[: [: ~A, ~B :], [: ~C, ~D :] :], [: A, B, C, D :]})
     c{i,o}
     @(split_nested_seq_core (~A) (~B) (~C) (~D))(o,i)
