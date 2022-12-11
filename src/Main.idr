module Main

import System.File.ReadWrite

import Day05.Input
import Day05.Domain
import Day05.Part1
import Day05.Part2

mkMove : (Nat,Nat,Nat) -> Move
mkMove (many,from,to) = MkMove from to many

partial
main : IO ()
main = do
  putStrLn "Hello 2022!"
  Right contents <- readFile "input"
    | Left err => putStrLn $ show err
  let inp1 = Input.read1 contents
  let moves = map mkMove inp1
  putStrLn "Input: \{show inp1}"
  putStrLn "Part1: \{show !(Part1.code moves)}"
  putStrLn "Part2: \{show !(Part2.code moves)}"
  -- putStrLn "Part2: \{show (Part2.partlyOverlaps inp1)}"
  pure ()

