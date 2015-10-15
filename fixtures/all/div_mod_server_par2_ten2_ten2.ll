div_mod_server_par2_ten2_ten2 = proc(r : [?Int, ?Int], s : [!Int, !Int])
  r[rm,rn]
  s[sdiv,smod]
  ( recv rm (m : Int)
  | recv rn (n : Int)).
  ( send sdiv (m / n)
  | send smod (m % n))
