wrong_order_sequence =
  \ (A: Type)(n: Int)->
  proc(c: [: [: ?A ^ n :], [: !A ^ n :] :])
    split c as [: a, b   :].
    split a as [: ai ^ n :].
    split b as [: bi ^ n :].
    sequence ^ n (
      let x: A <- ai.
      bi <- x
    )
