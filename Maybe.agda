module Maybe where

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just_   : A -> Maybe A

pure : {A : Set} -> A -> Maybe A
pure x = Just x

infix 5 _>>=_

_>>=_ : {A B : Set} -> Maybe A -> (A -> Maybe B) -> Maybe B
Nothing  >>= y = Nothing
(Just x) >>= y = y x

appMaybe : {A B C : Set} -> Maybe A -> Maybe B -> (A -> B -> C) -> Maybe C
appMaybe Nothing _ _         = Nothing
appMaybe _ Nothing _         = Nothing
appMaybe (Just x) (Just y) f = Just (f x y)
