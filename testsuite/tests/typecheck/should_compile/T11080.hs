{-# LANGUAGE KindsWithoutData, GADTSyntax, TypeFamilies #-}
module T11080 where

-- closed kind using H98 syntax
data kind Universe = Sum  Universe Universe
                   | Prod Universe Universe

-- closed kind using GADTs syntax
data kind Universe' where
    Sum'  :: Universe' -> Universe' -> Universe'
    Prod' :: Universe' -> Universe' -> Universe'

-- if this works then -XKindsWithoutData correctly implies -XDataKinds
type family F (a :: Universe) :: Bool where
  F (Sum  _ _) = 'True
  F (Prod _ _) = 'False
