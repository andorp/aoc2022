module Day04.Part1

public export
Section : Type
Section = (Int,Int)

overlaps : Section -> Section -> Bool
overlaps (a,b) (c,d) = (a <= c && d <= b) || (c <= a && b <= d)

export
fullyOverlaps : List (Section, Section) -> Int
fullyOverlaps = sum . map (trueIsOne . uncurry overlaps)
  where
    trueIsOne : Bool -> Int
    trueIsOne True  = 1
    trueIsOne False = 0
