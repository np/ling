showMult = \(m n : Int) ->
  (showInt m) ++S " * " ++S (showInt n) ++S " = " ++S showInt (m * n)

showDiv = \(m n : Double) ->
  (showDouble m) ++S " / " ++S (showDouble n) ++S " = " ++S showDouble (m /D n)

my42 : String = showMult 2 21

my3_14 : String = showDiv 6.28 2.0

myNewline : Char = '\n'
