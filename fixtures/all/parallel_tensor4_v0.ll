-- Needs mix
-- [c,d],[e,f] <mix> [c,d,e,f] <split> [c,e],[d,f] <split/split> [c],[e] and [d],[f]
parallel_tensor4_v0 = proc(cd : [!Int,!Int], ef : [!Int,!Int])
  cd[c,d]
  ef[e,f]
  ( ( send c 1 | send e 2 )
  | ( send d 3 | send f 4 )
  )
