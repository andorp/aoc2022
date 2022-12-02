module Day02.Part2

import Day02.Input
import Day02.Domain

||| 
export
defeats : RPS -> Defeats -> RPS
defeats Rock        Draw   = Rock 
defeats Paper       Loses  = Rock 
defeats Scrissors   Beats  = Rock 
defeats Rock        Beats  = Paper 
defeats Paper       Draw   = Paper 
defeats Scrissors   Loses  = Paper 
defeats Rock        Loses  = Scrissors 
defeats Paper       Beats  = Scrissors 
defeats Scrissors   Draw   = Scrissors

0
wellFormedDefeats : (x : RPS) -> (d : Defeats) -> GameRules (defeats x d, x, d)
wellFormedDefeats Rock Beats      = PR
wellFormedDefeats Rock Draw       = RR
wellFormedDefeats Rock Loses      = SR
wellFormedDefeats Paper Beats     = SP
wellFormedDefeats Paper Draw      = PP
wellFormedDefeats Paper Loses     = RP
wellFormedDefeats Scrissors Beats = RS
wellFormedDefeats Scrissors Draw  = SS
wellFormedDefeats Scrissors Loses = PS

partial
examples2 : IO ()
examples2 = do
  printLn (roundScore (elfCode 'A') (defeats (elfCode 'A') (yourGoalCode 'Y')), 4)
  printLn (roundScore (elfCode 'B') (defeats (elfCode 'B') (yourGoalCode 'X')), 1)
  printLn (roundScore (elfCode 'C') (defeats (elfCode 'C') (yourGoalCode 'Z')), 7)

export
calculateScore : List (RPS, Defeats) -> Score
calculateScore = foldl rscore 0
  where
    rscore : Score -> (RPS, Defeats) -> Score
    rscore s (e,y) = s + roundScore e (defeats e y)
