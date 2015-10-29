par_loli_ten_send_v2 =
 \(S T : Type)->
 proc(c : {!S,!T} -o [!S,!T])
  c{i,o}
  i[rs,rt]
  ( recv rs (vs : S)
  | recv rt (vt : T)).
  o[ss,st]
  ( send ss vs
  | send st vt)
