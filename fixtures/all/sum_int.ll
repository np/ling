sum_int = proc(a : {?Int ^ 10}, r : !Int)
  new/alloc (acc :* Int).
  acc <- 0.
  split acc as [: acci ^ 10, accn :].
  split a   as {  ai   ^ 10 }.
  sequence ^ 10 with i (
    let x : Int <- ai.
    let y : Int <- acci.
    acci <- (x + y)
  ).
  fwd(?Int)(accn, r)

