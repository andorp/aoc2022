module Main

import System.File.ReadWrite

import Day04.Input
import Day04.Part1
import Day04.Part2

partial
main : IO ()
main = do
  putStrLn "Hello 2022!"
  Right contents <- readFile "input"
    | Left err => putStrLn $ show err
  let inp1 = Input.read1 contents
  putStrLn "Input: \{show inp1}"
  putStrLn "Part1: \{show (Part1.fullyOverlaps inp1)}"
  -- let inp2 = Input.read2 contents
  -- -- printLn inp2
  putStrLn "Part2: \{show (Part2.partlyOverlaps inp1)}"
  pure ()

