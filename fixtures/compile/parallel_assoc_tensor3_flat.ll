parallel_assoc_tensor3_flat (cde : [!Int, !Int, !Int]) =
  cde[c,d,e]
  ( send c 1
  | send d 2
  | send e 3
  ).
