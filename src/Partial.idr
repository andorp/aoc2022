module Partial

%default partial

export
fromJust : Maybe a -> a
fromJust (Just x) = x

export
unsafeHead : List a -> a
unsafeHead (x :: xs) = x

export
last : List a -> a
last (x :: []) = x
last (x :: xs) = last xs

export
fromRight : Either a b -> b
fromRight (Right x) = x