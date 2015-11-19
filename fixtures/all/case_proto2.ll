dbl = \(n : Int)-> n + n
case_proto2 =
  \(S : Session)
   (n : Int)
   (p : < S ^ (n + n) >)
   (q : < S ^ (dbl n) >)
   (b : Bool)->
   proc(c)
   @(case b of
       `true  -> p
       `false -> q
   )(c)
