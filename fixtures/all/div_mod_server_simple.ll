div_mod_server_simple = proc(rm : ?Int, rn : ?Int, sdiv : !Int, smod : !Int)
  recv rm (m : Int).
  recv rn (n : Int).
  send sdiv (m / n).
  send smod (m % n)
