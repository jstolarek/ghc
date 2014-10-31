module FullerLaziness ( fullerLaziness ) where

import CoreSyn
import DynFlags

fullerLaziness :: DynFlags -> CoreProgram -> CoreProgram
fullerLaziness _ = id
