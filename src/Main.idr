module Main

import System.File.ReadWrite

import Day06.Input
import Day06.Domain
import Day06.Part1
import Day06.Part2

import Data.Vect

partial
main : IO ()
main = do
  putStrLn "Hello 2022!"
  Right contents <- readFile "input"
    | Left err => putStrLn $ show err
  -- putStrLn "Test: \{show testData}"
  putStrLn "Test1: \{show (Part1.startOfPacketIndex $ Input.read1 testInput)}"
  putStrLn "Test2: \{show (Part2.startOfMessageIndex $ Input.read2 testInput)}"
  let blocks = Input.read1 contents
  putStrLn "Part1: \{show (Part1.startOfPacketIndex blocks)}"
  let messages = Input.read2 contents
  putStrLn "Part2: \{show (Part2.startOfMessageIndex messages)}"
  pure ()

