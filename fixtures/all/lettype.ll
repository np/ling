lettype
  : (P : (A B : Type)-> Type)
    (p : (A : Type)-> P A A)
    (A : Type)->
    P (P (P (P A A) (P A A)) (P (P A A) (P A A)))
      (P (P (P A A) (P A A)) (P (P A A) (P A A)))
  =
   \(P : (A B : Type)-> Type)
    (p : (A : Type)-> P A A)
    (A : Type)->
    let B = P A A in
    let C = P B B in
    let D = P C C in
    p D
