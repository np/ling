another_not : (x : Bool)-> Bool
    = \(x : Bool)-> case x of { `false -> `true, `true -> `false }

pnot = proc(c : ?Bool. !Bool)
  recv c (x : Bool)
  send c (case x of { `false -> `true, `true -> `false })

if : (b : Bool)(A : Type)(t e : A)-> A
   = \(b : Bool)(A : Type)(t e : A)->
      case b of { `true -> t, `false -> e }

If : (b : Bool)(A B : Type)(t : A)(e : B)->
      case b of { `true -> A, `false -> B }
   = \(b : Bool)(A B : Type)(t : A)(e : B)->
      case b of { `true -> t, `false -> e }

{-
Rejected:

if : (b : Bool)(A : Type)(t e : A)->
      case b of { `true -> A, `false -> A }
   = \(b : Bool)(A : Type)(t e : A)->
      case b of { `true -> t, `false -> e }

IF : (b : Bool)(A : (b : Bool)-> Type)(t : A `true)(e : A `false)-> A b
   = \(b : Bool)(A : (b : Bool)-> Type)(t : A `true)(e : A `false)->
      case b of { `true -> t, `false -> e }
-}

assert not `true = `false
assert not `false = `true
assert `false &&  `false = `false
assert `false &&  `true  = `false
assert `true  &&  `false = `false
assert `true  &&  `true  = `true
assert `false ||  `false = `false
assert `false ||  `true  = `true
assert `true  ||  `false = `true
assert `true  ||  `true  = `true
assert `false ==B `false = `true
assert `false ==B `true  = `false
assert `true  ==B `false = `false
assert `true  ==B `true  = `true
assert `false /=B `false = `false
assert `false /=B `true  = `true
assert `true  /=B `false = `true
assert `true  /=B `true  = `false
