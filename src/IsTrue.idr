module IsTrue


||| Check for True evaluation.
|||
||| This is a little helper to bring knowlege into the constructive proofs about '<' and '>='
public export
data IsTrue : Bool -> Type where
  YesIsTrue : IsTrue True

||| When something evaluates to True, it is also IsTrue
export
isTrueR : x === True -> IsTrue x
isTrueR Refl = YesIsTrue
