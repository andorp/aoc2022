module Main

import System.File.ReadWrite

import Day03.Domain
import Day03.Input
import Day03.Part1
import Day03.Part2

partial
main : IO ()
main = do
  putStrLn "Hello 2022!"
  Right contents <- readFile "input"
    | Left err => putStrLn $ show err
  let inp1 = Input.read1 contents
  -- putStrLn "Input: \{show inp1}"
  putStrLn "Part1: \{show (Part1.sumPriorities inp1)}"
  let inp2 = Input.read2 contents
  -- printLn inp2
  putStrLn "Part2: \{show (Part2.groupPriorities inp2)}"
  pure ()

