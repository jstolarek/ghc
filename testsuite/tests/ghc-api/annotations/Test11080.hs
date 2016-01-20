{-# LANGUAGE KindsWithoutData, TypeInType, GADTSyntax #-}
module Test11080 where

import Data.Kind

-- closed kind using H98 syntax
data kind Universe = Sum  Universe Universe
                   | Prod Universe Universe
                   | K (*)

-- closed kind using GADTs syntax
data kind Universe' where
    Sum'  :: Universe' -> Universe' -> Universe'
    Prod' :: Universe' -> Universe' -> Universe'
    K'    :: *                      -> Universe'
