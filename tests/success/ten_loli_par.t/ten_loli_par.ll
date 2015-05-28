ten_loli_par (c : [!Int,!Int] -o {!Int,!Int}) =
  c{i,o}
  i{i0,i1}
  o{o0,o1}
  ( fwd (?Int)(i0,o0)
  | fwd (?Int)(i1,o1)
  ).
