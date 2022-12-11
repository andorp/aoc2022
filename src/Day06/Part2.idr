module Day06.Part2

import Partial
import Decidable.Decidable
import Data.List
import Data.Fin
import Day06.Domain

export
partial
startOfMessageIndex : List Message -> Nat
startOfMessageIndex bs = sizeOfMessage + (finToNat $ fromJust $ findIndex isStart bs)
  where
    isStart : Message -> Bool
    isStart m = isYes $ isStartOfMessage m
