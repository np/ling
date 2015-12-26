-- See https://github.com/np/ling/issues/4
com_with_log =
 \(S : Session)
  (p : <      S >)
  (q : <     ~S >)
  (s : < ~Log S >)->
  proc()
  new(c : S,      c' : ~S)
  new(d : ~S,     d' : S)
  new(l : ~Log S, l' : Log S)
  ( @p(c)
  | @q(d)
  | @s(l)
  | fwd S (d',c',l'))
