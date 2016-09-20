tabulate_ten =
  \ (A : Type)(f : (i : Int)-> A)(n : Int)->
  proc(c : [ !A ^ n ])
    split c as [ c_ ^ n ]
    parallel ^ n with i (c_ <- (f i))

replicate_ten_10 = tabulate_ten Int (id Int) 10
