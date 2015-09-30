par_loli_ten_send =
 \(S : Type)(T : Type)->
 proc(c : {!S,!T} -o [!S,!T])
  c{i,o}
  i[rs,rt]
  o[ss,st]
  (recv rs (vs : S) | recv rt (vt : T))
  (send ss vs       | send st vt)
