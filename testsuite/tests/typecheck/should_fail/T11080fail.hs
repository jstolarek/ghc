-- JSTOLAREK: some language extension here
{-# LANGUAGE GADTSyntax #-}
module T11080fail where

data kind Foo = Bar

-- this should be rejected
foo :: Foo
foo = Bar

data kind Foo' where
    Bar'  :: Foo'

bar :: Foo'
bar = Bar'
