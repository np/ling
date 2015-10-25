test_pat_term2 =
  proc(abcde : [!Int, [: !Int, !Int :], { [!Int, !Int], {?Int, ?Int} } ])
    abcde[a, bc, de]
    bc[: b, c :]
    de{d, e}
    (send a 1 | send b 2. send c 3 | fwd [!Int,!Int] (d,e))

-- notice how various parts gets commuted
-- but also c and b which must stay in-order
wrong_test_pat =
  proc(bcaed : [[: !Int, !Int :], !Int, { {?Int, ?Int}, [!Int, !Int] } ])
    bcaed[bc, a, ed]
    bc[: b, c :]
    ed{e, d}
  @test_pat_term2[a, [: c, b :], {d, e}]
