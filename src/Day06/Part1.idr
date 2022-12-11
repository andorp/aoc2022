module Day06.Part1

import Partial
import Decidable.Decidable
import Data.List
import Data.Fin
import Day06.Domain

export
partial
startOfPacketIndex : List Block -> Nat
startOfPacketIndex bs = sizeOfBlock + (finToNat $ fromJust $ findIndex isStart bs)
  where
    isStart : Block -> Bool
    isStart b = isYes $ isStartOfPacket b
