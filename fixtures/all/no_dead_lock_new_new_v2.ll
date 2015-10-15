-- Requires a mix
no_dead_lock_new_new_v2 = proc()
  new (c : ?Int, d)
  new (e : ?Int, f)
  ( send d 5
  | ( recv c (x : Int).
      send f x
    | recv e (y : Int)))
