wrong_order_par2_par2 (c : [: {!Int,!Int}, {!Int,!Int} :]) =
  c[:d,e:]
  d{f,g}
  e{h,i}
  send g 2
  send h 3
  send i 4
  send f 1

