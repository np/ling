par_ten_ten_v1 (c : {[?Int, !Int], [!Int, ?Int]}) =
  c{e,d} d[k,l] e[h,g]
  ( recv h (x : Int)
  | send k 1
  | recv l (y : Int)
  | send g 2
  ).
