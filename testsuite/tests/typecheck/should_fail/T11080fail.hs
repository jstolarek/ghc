{-# LANGUAGE KindsWithoutData, GADTSyntax #-}
module T11080fail where

data kind Foo = Bar

data kind Foo' where
    Bar'  :: Foo'

foo :: Foo
foo = Bar

bar :: Foo'
bar = Bar'
