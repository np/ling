-- plug_compose_par_par is a variation over plug_compose which is derived from
-- plug_compose. This shows how one can convert between <A,B> and <{A,B}>.

flat_par' =
  \(A B : Session)
   (p : < {A, B} >)->
  proc(a : A, b : B)
    new(ab : {A, B}, nanb)
    ( @p(ab)
    | nanb[na,nb]
      ( fwd(A)(a,na)
      | fwd(B)(b,nb)))

bump_par' =
  \(A B : Session)
   (p : < A, B >)->
  proc(ab : {A, B})
    ab{a,b}
    @p(a,b)

plug_compose' =
  \(A B C : Session)
   (p : < A, B >)
   (q : < ~B, C >)->
  proc(a : A, c : C)
    new(b : B, b' : ~B)
    ( @p(a, b)
    | @q(b', c))

plug_compose_par_par :
   (A B C : Session)
   (p : < { A, B} >)
   (q : < {~B, C} >)->
        < { A, C} >
  =
  \(A B C : Session)
   (p : < { A, B} >)
   (q : < {~B, C} >)->
   bump_par' A C (plug_compose' A B C (flat_par' A B p) (flat_par' (~B) C q))
