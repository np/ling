With  = \(SL SR : Session)-> ?(b : LR). (case b of { `left -> SL, `right -> SR })
with =
  \(SL SR : Session)
   (pL : < SL >)(pR : < SR >)->
  proc(c : With SL SR)
    recv c (x : LR).
    @(case x of { `left -> pL, `right -> pR })(c)
