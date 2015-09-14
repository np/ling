wrong_order_seq_seq_send2 (a : [:[:!Int.!Int,!Int.!Int:],!Int.!Int:]) =
  a[:b,e:] b[:c,d:] send c 1 send c 2 send d 3 send e 4 send d 5 send e 6.
