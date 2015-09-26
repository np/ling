wrong_order_par_seq_front (a : {[:!Int,!Int:],!Int}) =
  a{b,e} b[:c,d:] send e 1 send d 3 send c 2
