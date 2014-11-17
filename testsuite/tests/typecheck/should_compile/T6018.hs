{-# LANGUAGE TypeFamilies, DataKinds, UndecidableInstances, PolyKinds #-}

module T6018 where

import T6018a -- defines G, identical to F

type family F a b c = (result :: *) | result -> a b c
type instance F Int  Char Bool = Bool
type instance F Char Bool Int  = Int
type instance F Bool Int  Char = Char
type instance F Bool Int  Char = Char

type instance G Bool Int  Char = Char

type family I (a :: *) b (c :: *) = r | r -> a b
type instance I Int  Char Bool = Bool
type instance I Int  Char Int  = Bool
type instance I Bool Int  Int  = Int

-- this is injective - a type variables mentioned on LHS is not mentioned on RHS
-- but we don't claim injectivity in that argument.
type family J a (b :: k) = r | r -> a
type instance J Int b = Char

type MaybeSyn a = Maybe a
type family K a = r | r -> a
type instance K a = MaybeSyn a
