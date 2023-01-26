module Main

-- import System.File.ReadWrite

import Day11.TestInput
import Day11.Input
--import Day11.Domain
-- import Day11.Domain
-- import Day11.Part1
import Day11.Part1
import Day11.Part2
import Day11.Part1b
import Day11.Part2b

-- import Day11.Domain3

-- import Partial
-- import Data.Vect

partial
main : IO ()
main = do
  -- putStrLn "Hello 2022!"
  -- Right testInput <- readFile "test-input2"
  --   | Left err => putStrLn $ show err
  -- let testInputData = Input.read testInput
  -- Right contents <- readFile "input"
  --   | Left err => putStrLn $ show err

  -- Part1.test1 testInputData
  putStrLn "Part1: \{show !(Part1.part1 TestInput.monkeys1)}"
  putStrLn "Part2: \{show !(Part2.part2 TestInput.monkeys2)}"

  -- let inp = Input.read contents
  putStrLn "Part1: \{show !(Part1.part1 Input.monkeys1)}"
  putStrLn "Part2: \{show !(Part2.part2 Input.monkeys2)}"

  putStrLn "Part1: \{show !(Part1b.part1 Input.monkeys3)}"
  -- putStrLn "Part2: \{show !(Part2b.part2 Input.monkeys3)}"
  -- Issue: Exception in string-append: erased is not a string

  pure ()


