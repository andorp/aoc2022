module Main

import System.File.ReadWrite

import Day10.Input
import Day10.Domain
import Day10.Part1
import Day10.Part2
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
  let prg = input
  putStrLn "Part1: \{show !(part1 prg)}"
  putStrLn "Part2:"
  part2 prg
  pure ()

