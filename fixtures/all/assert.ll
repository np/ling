assert `false = `false : Bool

assert (\(x:Bool) -> x) = (\(y:Bool) -> y) : ((b:Bool) -> Bool)

not : (x : Bool)-> Bool
    = \(x : Bool)-> case x of { `false -> `true, `true -> `false }

assert (not `true) = `false : Bool

assert
    (proc (r : ?Bool.!Bool)
      (recv r (x : Bool) . send r x))
  = (proc (r : ?Bool.!Bool)
      (recv r (y : Bool) . send r y))
  : < ?Bool . !Bool >

assert
    (proc (r : !Bool) (send r (not `true)))
  = (proc (r : !Bool) (send r `false))
  : < !Bool >
