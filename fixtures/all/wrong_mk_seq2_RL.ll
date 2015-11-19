wrong_mk_seq2_RL =
  \ (S0 S1 : Session)
    (p0 : < S0 >)
    (p1 : < S1 >)->
  proc(c : [: S0, S1 :])
    c[: c0, c1 :]
    @p1(c1).
    @p0(c0)
