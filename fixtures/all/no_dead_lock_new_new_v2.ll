-- Requires a mix
no_dead_lock_new_new_v2 =
  new (c : ?Int, d)
  new (e : ?Int, f)
  -- split [e] and [c,d],[f]
  ( send d 5
  -- split [c],[f] and [d]
  | ( recv c (x : Int)
      send f x
    | recv e (y : Int)
    )
  ).
