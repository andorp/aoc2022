module Day11.TestInput

import Day11.Domain1
import Day11.Domain2
import Day11.Domain3
import Data.Vect

export
monkeys1 : Vect 4 (Domain1.Monkey 4)
monkeys1 =
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

export
monkeys2 : Vect 4 (Domain2.Monkey 0 4)
monkeys2 =
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

export
monkeys3 : (Num n) => Vect 4 (Domain3.Monkey n 4)
monkeys3 =
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
