-- should be infix _-:_
seqi = \(S0 S1 : Session)-> [: ~S0, S1 :]

par_seqi_ten_send =
 \(A B : Type)->
 proc(c : seqi {!A,!B} [!A,!B])
  c[:i,o:]
  i[rs,rt]
  o[ss,st]
  ( recv rs (vs : A)
  | recv rt (vt : B)).
  ( send ss vs
  | send st vt)
