module Day11.TestInput

import Day11.Domain
import Data.Vect

{-
  , MkMonkey
    { items = 
    , brain = MkBrain
      { operation = 
      , divisible = 
      , ifTrue    = 
      , ifFalse   = 
      }
    }
-}

export
monkeys : Vect 4 (Monkey 4)
monkeys =
  [ MkMonkey
    { items = [79, 98]
    , brain = MkBrain
      { operation = (*19)
      , divisible = 23
      , ifTrue    = 2
      , ifFalse   = 3
      }
    }
  , MkMonkey
    { items = [54, 65, 75, 74]
    , brain = MkBrain
      { operation = (+6)
      , divisible = 19
      , ifTrue    = 2
      , ifFalse   = 0
      }
    }
  , MkMonkey
    { items = [79, 60, 97]
    , brain = MkBrain
      { operation = \old => old * old
      , divisible = 13
      , ifTrue    = 1
      , ifFalse   = 3
      }
    }
  , MkMonkey
    { items = [74]
    , brain = MkBrain
      { operation = (+3)
      , divisible = 17
      , ifTrue    = 0
      , ifFalse   = 1
      }
    }                
  ]