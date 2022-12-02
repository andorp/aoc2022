module Main

import System.File.ReadWrite

import Day02.Domain
import Day02.Input
import Day02.Part1
import Day02.Part2

partial
main : IO ()
main = do
  putStrLn "Hello 2022!"
  Right contents <- readFile "input"
    | Left err => putStrLn $ show err
  let inp1 = Input.read1 contents
  -- putStrLn "Input: \{show inp}"
  putStrLn "Part1: \{show (Part1.calculateScore inp1)}"
  let inp2 = Input.read2 contents
  putStrLn "Part2: \{show (Part2.calculateScore inp2)}"
  pure ()

