let_example =
   let T = Int in
   let f = _+_ in
   proc(c : ?T.!T)
   recv c (x : T).
   let y = (f x x).
   send c y
