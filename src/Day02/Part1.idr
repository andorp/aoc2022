module Day02.Part1

import Day02.Input
import Day02.Domain

partial
examples1 : IO ()
examples1 = do
  printLn (roundScore (elfCode 'A') (yourCode 'Y'), 8)
  printLn (roundScore (elfCode 'B') (yourCode 'X'), 1)
  printLn (roundScore (elfCode 'C') (yourCode 'Z'), 6)


export
calculateScore : List (RPS, RPS) -> Score
calculateScore = foldl rscore 0
  where
    rscore : Score -> (RPS, RPS) -> Score
    rscore s (e,y) = s + roundScore e y
