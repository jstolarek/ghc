{-# LANGUAGE TypeFamilies #-}

module T6018rnfail where

-- ID = injectivity declaration `| foo -> bar`

-- use incorrect tyvar in LHS of ID
type family F a = r | a -> a
type family Fc a = r | a -> a where
  Fc a = a
class Fcl a where
  type Ft a = r | a -> a

-- declare result tyvar to be duplicate (without ID)
type family G a = a
type family Gc a = a where
  Gc a = a
class Gcl a where
  type Gt a = a

-- declare result tyvar to be duplicate (with ID)
type family Gb a = a | a -> a
type family Gcb a = a | a -> a where
  Gcb a = a
class Gclb a where
  type Gtb a = a | a -> a

-- incorrect order of tyvars in RHS of ID
type family H a b = r | r -> b a
type family Hc a b = r | r -> b a where
  Hc a b = a
class Hcl a b where
  type Ht a b = r | r -> b a

-- not in-scope tyvar in RHS of ID
type family I a b = r | r -> c
type family Ic a b = r | r -> c where
  Ic a b = a
class Icl a b where
  type It a b = r | r -> c

-- repeated tyvar on RHS of ID
type family J a b = r | r -> a a
type family Jc a b = r | r -> a a where
  Jc a b = a
class Jcl a b where
  type Jt a b = r | r -> a a

-- too many tyvars on RHS of ID
type family K a b = r | r -> a b b
type family Kc a b = r | r -> a b b where
  Kc a b = a
class Kcl a b where
  type Kt a b = r | r -> a b b

-- not in-scope tyvar in LHS of ID
type family L a b = r | c -> a
type family Lc a b = r | c -> a where
  Lc a b = a
class Lcl a b where
  type Lt a b = r | c -> a
