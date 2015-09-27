parallel_tensor4_flat = proc(cd : [!Int,!Int], ef : [!Int,!Int])
  cd[c,d]
  ef[e,f]
  ( send c 1
  | send e 2
  | send d 3
  | send f 4
  )
