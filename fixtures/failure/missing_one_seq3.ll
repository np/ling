missing_one_seq3 (c : [: !Int, !Int, !Int :]) =
  c[: c0, c1, c2 :]
  send c1 1
  send c2 2
.
