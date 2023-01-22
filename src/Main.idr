module Main

import System.File.ReadWrite

import Day11.TestInput
import Day11.Input
import Day11.Domain
import Day11.Part1
import Day11.Part2
import Partial

partial
main : IO ()
main = do
  putStrLn "Hello 2022!"
  -- Right testInput <- readFile "test-input2"
  --   | Left err => putStrLn $ show err
  -- let testInputData = Input.read testInput
  -- Right contents <- readFile "input"
  --   | Left err => putStrLn $ show err

  -- Part1.test1 testInputData
  -- putStrLn "Part1 test: \{show !(part1 (Input.read testInput))}"
  -- putStrLn "Part2 test: \{show !(part2 (Input.read testInput))}"

  -- let inp = Input.read contents
  -- putStrLn "Part1: \{show !(part1 Input.monkeys)}"
  putStrLn "Part2: \{show !(part2 TestInput.monkeys)}"
  -- putStrLn "Part2:"
  -- part2 prg
  pure ()

