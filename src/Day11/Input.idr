module Day11.Input

import Day11.Domain1
import Day11.Domain2
import Day11.Domain3
import Data.Vect


export
monkeys1 : Vect 8 (Domain1.Monkey 8)
monkeys1 =
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
      { operation = \x => (x * x)
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

export
monkeys2 : Vect 8 (Domain2.Monkey 0 8)
monkeys2 =
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
      { operation = \x => (x * x)
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

export
monkeys3 : Num n => Vect 8 (Domain3.Monkey n 8)
monkeys3 =
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
      { operation = \x => (x * x)
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
