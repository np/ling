assert
    `true
  = `true : let B = Bool in
            case `left of { `left -> B, `right -> Int }
