module Day11.Part1b

import Day11.Domain3
import Data.Vect

decreaseWorry : WorryChange Int
decreaseWorry = mkWorryChange (\i => i `div` (the Int 3))

export
part1 : {n : Nat} -> Vect n (Monkey Int n) -> IO ()
part1 monkeys = simulation Int decreaseWorry monkeys 20
