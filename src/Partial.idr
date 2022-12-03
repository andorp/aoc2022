module Partial

%default partial

export
fromJust : Maybe a -> a
fromJust (Just x) = x

export
unsafeHead : List a -> a
unsafeHead (x :: xs) = x
