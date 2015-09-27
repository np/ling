par_ten_ten_v2 = proc(c : {[?Int, !Int], [!Int, ?Int]})
  c{e,d} d[k,l] e[h,g]
  ( ( send k 1
    | ( recv h (x : Int) | recv l (y : Int) )
    )
  | send g 2
  )
