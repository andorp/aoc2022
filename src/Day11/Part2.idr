module Day11.Part2

import Day11.Domain2
import Data.Vect

-- data Modulo : Int -> Type where
--   MkModNum : {m : Int} -> (x : Int) -> Modulo m

-- mkModNum : {m : Int} -> Int -> Modulo m
-- mkModNum {m} x = MkModNum (x `mod` m)

-- {m : Int} -> IsDivisible (Modulo m) where
--   isDivible (MkModNum x) d = x `mod` d == 0

noChange : WorryChange
noChange = mkWorryChange id

calcDivisor : Vect n (Monkey 0 n) -> Int
calcDivisor = foldl (\p , m => p * m.brain.divisible) 0

moduloBrain : (m : Int) -> MonkeyBrain 0 n -> MonkeyBrain m n
moduloBrain m x = MkBrain
  { divisible = x.divisible
  , operation = x.operation
  , ifTrue    = x.ifTrue
  , ifFalse   = x.ifFalse
  }

moduleMonkey : (m : Int) -> Monkey 0 n -> Monkey m n
moduleMonkey m x = MkMonkey
  { brain = moduloBrain m x.brain
  , items = x.items
  }

export
part2 : {n : Nat} -> Vect n (Monkey 0 n) -> IO ()
part2 monkeys = simulation noChange monkeys 10000
