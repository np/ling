ten_loli_par =
 \(A B : Session)->
 proc(c : [A,B] -o {A,B})
  c{i,o}
  i{na,nb}
  o{a,b}
  ( fwd(A)(a,na)
  | fwd(B)(b,nb))

ten_loli_par_sInt_sDouble = ten_loli_par (!Int) (!Double)
