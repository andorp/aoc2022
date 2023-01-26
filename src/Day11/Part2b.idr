module Day11.Part2b

import Day11.Domain3
import Data.Vect

export
data Modulo : Int -> Type where
  MkModNum : {m : Int} -> (x : Int) -> Modulo m

mkModNum : {m : Int} -> Int -> Modulo m
mkModNum {m} x = MkModNum (x `mod` m)

export
{m : Int} -> Num (Modulo m) where
  fromInteger = mkModNum . fromInteger
  (MkModNum a) + (MkModNum b) = mkModNum (a+b)
  (MkModNum a) * (MkModNum b) = mkModNum (a*b)

export
{m : Int} -> Show (Modulo m) where
  show (MkModNum {m} x) = "" -- show x -- ++ " % " ++ show m

export
{m : Int} -> IsDivisible (Modulo m) where
  isDivible (MkModNum x) d = x `mod` d == 0

noChange : WorryChange (Modulo m)
noChange = mkWorryChange id

calcDivisor : Vect n (Monkey Int n) -> Int
calcDivisor = foldl (\p , m => p * m.brain.divisible) 0

moduloBrain : Int -> MonkeyBrain Int n -> MonkeyBrain (Modulo m) n
moduloBrain m x = MkBrain
  { divisible = x.divisible
  , operation = \case (MkModNum i) => mkModNum (x.operation i)
  , ifTrue    = x.ifTrue
  , ifFalse   = x.ifFalse
  }

moduleMonkey : (m : Int) -> Monkey Int n -> Monkey (Modulo m) n
moduleMonkey m x = MkMonkey
  { brain = moduloBrain m x.brain
  , items = map mkModNum x.items
  }

export
part2 : {n : Nat} -> Vect n (Monkey Int n) -> IO ()
part2 monkeys = do
  let m := calcDivisor monkeys
  simulation (Modulo m) noChange (map (moduleMonkey m) monkeys) 10000
