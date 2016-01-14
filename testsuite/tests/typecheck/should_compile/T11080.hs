-- JSTOLAREK: some language extension here
{-# LANGUAGE TypeInType #-}
module T11080 where

import Data.Kind

-- closed kind using H98 syntax
data kind Universe = Sum  Universe Universe
                   | Prod Universe Universe
                   | K (*)

-- JSTOLAREK: this should be rejected!
--foo :: Universe
--foo = Sum undefined undefined

{-
-- closed kind using GADTs syntax
data kind Universe where
    Sum  :: Universe -> Universe -> Universe
    Prod :: Universe -> Universe -> Universe
    K    :: *                    -> Universe
-}

{-
Things to test:

  * open data kinds declaration
  * make sure that type-level usage works
  * make sure that term-level use is rejected
  * make sure that things work between modules (interface files implemented
    correctly)
  * Check that indexing works
-}
