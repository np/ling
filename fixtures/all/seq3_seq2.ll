seq3_seq2 = proc(c : [: !Int, !Int, !Int :], d : [: !Int, !Int :])
  c[: c0, c1, c2 :]
  d[: d0, d1 :]
  send c0 0
  send c1 1
  send d0 0
  send c2 2
  send d1 1

