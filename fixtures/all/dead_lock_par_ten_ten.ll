dead_lock_par_ten_ten = proc(c : {[?Int, !Int], [!Int, ?Int]})
  c{d,e} d[h,g] e[k,l]
  ( recv h (x : Int) send k x
  | recv l (y : Int) send g y
  )
