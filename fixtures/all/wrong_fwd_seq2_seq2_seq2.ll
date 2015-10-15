wrong_fwd_seq2_seq2_seq2 =
  proc( i : [: ?Int, !Int.?Int :]
      , o : [: !Int, ?Int.!Int :]
      , l : {  !Int, !Int.!Int }
      )
  fwd [: ?Int,!Int.?Int :](i,o,l)
