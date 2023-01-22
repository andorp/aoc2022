module Day11.Part1

import Day11.Domain
import Data.Vect

decreaseWorry : WorryChange
decreaseWorry = mkWorryChange (\i => i `div` 3)

export
part1 : {n : Nat} -> Vect n (Monkey n) -> IO ()
part1 monkeys = simulation {worrying=decreaseWorry} monkeys 20