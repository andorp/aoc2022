module Day04.Part2

public export
Section : Type
Section = (Int,Int)

overlaps : Section -> Section -> Bool
overlaps (a,b) (c,d) = (a <= c && c <= b) || (c <= a && a <= d)

export
partlyOverlaps : List (Section, Section) -> Int
partlyOverlaps = sum . map (trueIsOne . uncurry overlaps)
  where
    trueIsOne : Bool -> Int
    trueIsOne True  = 1
    trueIsOne False = 0
