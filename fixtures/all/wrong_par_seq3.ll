wrong_par_seq3 = proc(c : [: !Int, !Int, !Int :])
  c[: c0, c1, c2 :]
  send c0 0
  (send c1 1 | send c2 2)

