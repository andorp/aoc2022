module Day02.Input

import Data.String

import Day02.Domain

export
partial
yourCode : Char -> RPS
yourCode 'X' = Rock
yourCode 'Y' = Paper
yourCode 'Z' = Scrissors

export
partial
yourGoalCode : Char -> Defeats
yourGoalCode 'X' = Loses
yourGoalCode 'Y' = Draw
yourGoalCode 'Z' = Beats

export
partial
elfCode : Char -> RPS
elfCode 'A' = Rock
elfCode 'B' = Paper
elfCode 'C' = Scrissors

partial
readPair : List Char -> (RPS, RPS)
readPair [e,' ',y] = (elfCode e, yourCode y)

export
partial
read1 : String -> List (RPS, RPS)
read1 = map (readPair . fastUnpack) . lines

partial
readPair2 : List Char -> (RPS, Defeats)
readPair2 [e,' ',y] = (elfCode e, yourGoalCode y)

export
partial
read2 : String -> List (RPS, Defeats)
read2 = map (readPair2 . fastUnpack) . lines
