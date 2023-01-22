module Day11.Input

import Day11.Domain
import Data.Vect

export
monkeys : Vect 8 (Monkey 8)
monkeys =
  [ 
    MkMonkey
    { items = [52, 78, 79, 63, 51, 94]
    , brain = MkBrain
      { operation = (*13)
      , divisible = 5
      , ifTrue    = 1
      , ifFalse   = 6
      }
    }
  , MkMonkey
    { items = [77, 94, 70, 83, 53]
    , brain = MkBrain
      { operation = (+3)
      , divisible = 7
      , ifTrue    = 5
      , ifFalse   = 3
      }
    }
  , MkMonkey
    { items = [98, 50, 76]
    , brain = MkBrain
      { operation = \old => old * old
      , divisible = 13
      , ifTrue    = 0
      , ifFalse   = 6
      }
    }
  , MkMonkey
    { items = [92, 91, 61, 75, 99, 63, 84, 69]
    , brain = MkBrain
      { operation = (+5)
      , divisible = 11
      , ifTrue    = 5
      , ifFalse   = 7
      }
    }
  , MkMonkey
    { items = [51, 53, 83, 52]
    , brain = MkBrain
      { operation = (+7)
      , divisible = 3
      , ifTrue    = 2
      , ifFalse   = 0
      }
    }
  , MkMonkey
    { items = [76, 76]
    , brain = MkBrain
      { operation = (+4)
      , divisible = 2
      , ifTrue    = 4
      , ifFalse   = 7
      }
    }
  , MkMonkey
    { items = [75, 59, 93, 69, 76, 96, 65]
    , brain = MkBrain
      { operation = (*19)
      , divisible = 17
      , ifTrue    = 1
      , ifFalse   = 3
      }
    }
  , MkMonkey
    { items = [89]
    , brain = MkBrain
      { operation = (+2)
      , divisible = 19
      , ifTrue    = 2
      , ifFalse   = 4
      }
    }
  ]
