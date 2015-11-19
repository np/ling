My_Int = Int
case_proto
  :  (x : Bool)-> < ?Int >
  = \(x : Bool)-> proc(c : ?Int)
  @(case x of
      `true  -> proc(d : ?Int)    recv d (y : Int)
      `false -> proc(e : ?My_Int) recv e (y : My_Int)
  )(c)
