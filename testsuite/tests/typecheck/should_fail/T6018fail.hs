{-# LANGUAGE TypeFamilies, DataKinds, UndecidableInstances #-}

module T6018fail where

import T6018Afail -- defines G, identical to F
import T6018Cfail -- imports H from T6018Bfail, defines some equations for H
import T6018Dfail -- imports H from T6018Bfail, defines conflicting eqns

type family F a b c = (result :: *) | result -> a b c
type instance F Int  Char Bool = Bool
type instance F Char Bool Int  = Int
type instance F Bool Int  Char = Int

type instance G Bool Int  Char = Int

type family I a b c = r | r -> a b
type instance I Int  Char Bool = Bool
type instance I Int  Int  Int  = Bool
type instance I Bool Int  Int  = Int

-- Id is injective...
type family Id a = result | result -> a
type instance Id a = a

-- ...but despite that we disallow a call to Id
type family IdProxy a = r | r -> a
type instance IdProxy a = Id a

data N = Z | S N

-- P is not injective, although the user declares otherwise. This
-- should be rejected on the grounds of calling a type family in the
-- RHS.
type family P (a :: N) (b :: N) = (r :: N) | r -> a b
type instance P  Z    m = m
type instance P (S n) m = S (P n m)

-- this is not injective - not all injective type variables mentioned
-- on LHS are mentioned on RHS
type family J a b c = r | r -> a b
type instance J Int b c = Char

-- same as above, but tyvar is now nested inside a tycon
type family K (a :: N) (b :: N) = (r :: N) | r -> a b
type instance K (S n) m = S m

type MaybeSyn a = Id a
type family L a = r | r -> a
type instance L a = MaybeSyn a
