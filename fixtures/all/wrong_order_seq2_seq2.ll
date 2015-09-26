wrong_order_seq2_seq2 (c : [: [: !Int,!Int :], [: !Int,!Int :] :]) =
  c[:d,e:]
  d[:f,g:]
  e[:h,i:]
  send h 3
  send i 4
  send f 1
  send g 2

