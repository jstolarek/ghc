{-# LANGUAGE KindsWithoutData, GADTSyntax, TypeFamilies #-}
module T11080 where

-- closed kind using H98 syntax
data kind Universe = Sum  Universe Universe
                   | Prod Universe Universe
                   | K

-- closed kind using GADTs syntax
data kind Universe' where
    Sum'  :: Universe' -> Universe' -> Universe'
    Prod' :: Universe' -> Universe' -> Universe'
    K'    :: Universe'

-- if this works then -XKindsWithoutData correctly implies -XDataKinds
type family F (a :: Universe) :: Bool where
  F (Sum  _ _) = 'True
  F (Prod _ _) = 'False

data kind open Dimension
data kind open Dimension' :: *
data kind open Unit :: Dimension -> *
data kind open Unit2 (a :: Dimension) :: *

-- make sure `kind` can be used as a variable and type variable name
foo :: kind -> kind
foo kind = kind
