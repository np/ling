fake_div_mod_server_ten2 = proc(r : [?Int, ?Int], s : [!Int, !Int])
  r[rm,rn]
  s[sdiv,smod]
  ( send sdiv 42
  | send smod 21).
  ( recv rm (m : Int)
  | recv rn (n : Int))
