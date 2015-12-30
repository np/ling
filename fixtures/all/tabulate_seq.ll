tabulate_seq =
  \ (A : Type)
    (f : (i : Int)-> A)
    (n : Int)->
  proc(a : [: !A^n :])
    split a [: a_i^n :].
    slice (a_i) n as i
      a_i <- (f i)

tabulate_seq_Double_40 =
  tabulate_seq Double (\(i : Int)-> 1.0 -D (0.05 *D Int2Double i)) 41
