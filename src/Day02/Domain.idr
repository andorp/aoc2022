module Day02.Domain

import Data.DPair

public export
data RPS = Rock | Paper | Scrissors

public export
data Defeats = Beats | Draw | Loses

public export
data GameRules : (RPS,RPS,Defeats) -> Type where
  RR : GameRules ( Rock       , Rock        , Draw  )
  RP : GameRules ( Rock       , Paper       , Loses )
  RS : GameRules ( Rock       , Scrissors   , Beats )
  PR : GameRules ( Paper      , Rock        , Beats )
  PP : GameRules ( Paper      , Paper       , Draw  )
  PS : GameRules ( Paper      , Scrissors   , Loses )
  SR : GameRules ( Scrissors  , Rock        , Loses )
  SP : GameRules ( Scrissors  , Paper       , Beats )
  SS : GameRules ( Scrissors  , Scrissors   , Draw  )

export
defeats : RPS -> RPS -> Defeats
defeats Rock       Rock        = Draw
defeats Rock       Paper       = Loses
defeats Rock       Scrissors   = Beats
defeats Paper      Rock        = Beats
defeats Paper      Paper       = Draw
defeats Paper      Scrissors   = Loses
defeats Scrissors  Rock        = Loses
defeats Scrissors  Paper       = Beats
defeats Scrissors  Scrissors   = Draw

0
wellFormedDefeats : (x,y : RPS) -> GameRules (x,y,defeats x y)
wellFormedDefeats Rock      Rock      = RR
wellFormedDefeats Rock      Paper     = RP
wellFormedDefeats Rock      Scrissors = RS
wellFormedDefeats Paper     Rock      = PR
wellFormedDefeats Paper     Paper     = PP
wellFormedDefeats Paper     Scrissors = PS
wellFormedDefeats Scrissors Rock      = SR
wellFormedDefeats Scrissors Paper     = SP
wellFormedDefeats Scrissors Scrissors = SS

oppositeDefeats : Defeats -> Defeats
oppositeDefeats Beats = Loses
oppositeDefeats Draw  = Draw
oppositeDefeats Loses = Beats

0
defeatsOppositeTheorem : (x,y : RPS) -> defeats x y === oppositeDefeats (defeats y x)
defeatsOppositeTheorem Rock       Rock      = Refl
defeatsOppositeTheorem Rock       Paper     = Refl
defeatsOppositeTheorem Rock       Scrissors = Refl
defeatsOppositeTheorem Paper      Rock      = Refl
defeatsOppositeTheorem Paper      Paper     = Refl
defeatsOppositeTheorem Paper      Scrissors = Refl
defeatsOppositeTheorem Scrissors  Rock      = Refl
defeatsOppositeTheorem Scrissors  Paper     = Refl
defeatsOppositeTheorem Scrissors  Scrissors = Refl

public export
Score : Type
Score = Int

score : RPS -> Score
score Rock      = 1
score Paper     = 2
score Scrissors = 3

gameScore : Defeats -> Score
gameScore Beats = 6
gameScore Draw  = 3
gameScore Loses = 0

export
roundScore : RPS -> RPS -> Score
roundScore e y = score y + gameScore (defeats y e)
