data Bool = `false | `true

not : (x : Bool)-> Bool
    = \(x : Bool)-> case x of { `false -> `true, `true -> `false }

pnot (c : ?Bool. !Bool) =
  recv c (x : Bool)
  send c (case x of { `false -> `true, `true -> `false })

if : (b : Bool)(A : Type)(t : A)(e : A)-> A
   = \(b : Bool)(A : Type)(t : A)(e : A)->
      case b of { `true -> t, `false -> e }

If : (b : Bool)(A : Type)(B : Type)(t : A)(e : B)->
      case b of { `true -> A, `false -> B }
   = \(b : Bool)(A : Type)(B : Type)(t : A)(e : B)->
      case b of { `true -> t, `false -> e }

{-
Rejected:

if : (b : Bool)(A : Type)(t : A)(e : A)->
      case b of { `true -> A, `false -> A }
   = \(b : Bool)(A : Type)(t : A)(e : A)->
      case b of { `true -> t, `false -> e }

IF : (b : Bool)(A : (b : Bool)-> Type)(t : A `true)(e : A `false)-> A b
   = \(b : Bool)(A : (b : Bool)-> Type)(t : A `true)(e : A `false)->
      case b of { `true -> t, `false -> e }
-}

