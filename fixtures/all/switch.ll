switch
  : (A B C : Session)->
    < [A, {B, C}] -o {[A, B], C} >
  = \(A B C : Session)->
    -- The definition of `-o` is expanded to make it easier to follow the splits.
    proc(c : {{~A, [~B, ~C]}, {[A, B], C}})
      c{i,o}
      i{na,nbc}
      nbc[nb,nc]
      o{ab,c}
      ab[a,b]
      ( fwd A (a,na)
      | fwd B (b,nb)
      | fwd C (c,nc))
