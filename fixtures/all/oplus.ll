Oplus' = \(SL SR : Session)-> !(b : LR). (case b of { `left -> SL, `right -> SR })

leftOplus =
  \(SL SR : Session)(p : < SL >)->
    proc(c)
    c : Oplus' SL SR <- `left.
    @p(c)

rightOplus =
  \(SL SR : Session)(p : < SR >)->
    proc(c)
    c : Oplus' SL SR <- `right.
    @p(c)

oplus' =
  \(SL SR : Session)
   (b : LR)
   (p : < case b of { `left -> SL, `right -> SR } >)->
    proc(c)
    c : Oplus' SL SR <- b.
    @p(c)

assert leftOplus
     = \(SL SR : Session)-> oplus' SL SR `left
     : (SL SR : Session)(p : < SL >)-> < Oplus' SL SR >

assert rightOplus
     = \(SL SR : Session)-> oplus' SL SR `right
     : (SL SR : Session)(p : < SR >)-> < Oplus' SL SR >
