compose_ops1 = \ (S T U : Session)(p : < S, T >)(q : < ~T, U >)->
  p =/|/= q
compose_ops2 = \ (S T U : Session)(p : < S, T >)(q : < U, ~T >)->
  p =/|=/ q
compose_ops3 = \ (S T U : Session)(p : < S, T >)(q : < ~S, U >)->
  p /=|/= q
compose_ops4 = \ (S T U : Session)(p : < S, T >)(q : < U >)->
  p ==|= q
compose_ops5 = \ (S T U : Session)(p : < S >)(q : < T, U >)->
  p =|== q
compose_ops6 = \ (S T U : Session)(p : < S >)(q : < T >)->
  p =|= q
compose_ops7 = \ (S T U : Session)(p : < S >)(q : < >)->
  p =| q
compose_ops8 = \ (S T U : Session)(p : < >)(q : < T >)->
  p |= q
compose_ops9 = \ (S T U : Session)(p : < >)(q : < T, U >)->
  p |== q

compose_ops11 = \ (S T U : Session)(p : < S, Send T >)(q : < ~Send T, U >)->
  p =/./= q
compose_ops12 = \ (S T U : Session)(p : < S, Send T >)(q : < U, ~Send T >)->
  p =/.=/ q
compose_ops13 = \ (S T U : Session)(p : < Send S, T >)(q : < ~Send S, U >)->
  p /=./= q
compose_ops14 = \ (S T U : Session)(p : < S, T >)(q : < U >)->
  p ==.= q
compose_ops15 = \ (S T U : Session)(p : < S >)(q : < T, U >)->
  p =.== q
compose_ops16 = \ (S T U : Session)(p : < S >)(q : < T >)->
  p =.= q
compose_ops17 = \ (S T U : Session)(p : < S >)(q : < >)->
  p =. q
compose_ops18 = \ (S T U : Session)(p : < >)(q : < T >)->
  p .= q
compose_ops19 = \ (S T U : Session)(p : < >)(q : < T, U >)->
  p .== q

compose_ops20 = \ (S T U V : Session)
                  (p : < S, Send T, Send U >)(q : < ~Send T, V, ~Send U >)->
  p =//./=/ q
