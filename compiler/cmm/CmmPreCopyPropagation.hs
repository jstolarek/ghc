{-# LANGUAGE GADTs #-}
module CmmPreCopyPropagation where

import Cmm
import CmmUtils
import DynFlags
import Hoopl
import UniqSupply

cmmPreCopyPropagation :: DynFlags -> CmmGraph -> UniqSM CmmGraph
cmmPreCopyPropagation dflags graph = do
     g' <- dataflowPassFwd graph [] $
           analRewFwd cpPreLattice cpPreTransfer (cpPreRewrite dflags)
     return . fst $ g'

data CpPreFact = CpPreFact

cpPreLattice :: DataflowLattice CpPreFact
cpPreLattice = DataflowLattice "preprocessing for copy propagation" CpPreFact cpPreJoin

cpPreJoin :: JoinFun CpPreFact
cpPreJoin _ _ _ = (NoChange, CpPreFact)

cpPreTransfer :: FwdTransfer CmmNode CpPreFact
cpPreTransfer = mkFTransfer3 (\_ f -> f) (\_ f -> f) distributeFact

cpPreRewrite :: DynFlags -> FwdRewrite UniqSM CmmNode CpPreFact
cpPreRewrite dflags = deepFwdRw3 nil (cpPreRwMiddle dflags) nil -- no need for deep. How to make shallow?
    where nil _ _ = return Nothing

cpPreRwMiddle :: DynFlags
              -> CmmNode O O
              -> CpPreFact
              -> UniqSM (Maybe (Graph CmmNode O O))
-- if we store a register or a literal don't do nothing - this will be dealt
-- with by copy propagation
cpPreRwMiddle _ (CmmStore _ (CmmReg _)) = const $ return Nothing
cpPreRwMiddle _ (CmmStore _ (CmmLit _)) = const $ return Nothing

-- otherwise we create a new register, assign previously stored expression to that
-- new register, and store the new register
cpPreRwMiddle dflags (CmmStore lhs rhs) = const $ do
  u <- getUniqueUs
  let regSize      = cmmExprType dflags rhs
      newReg       = CmmLocal $ LocalReg u regSize
      newRegAssign = CmmAssign newReg rhs
      newMemAssign = CmmStore lhs (CmmReg newReg)
  return . Just . GUnit . BCons newRegAssign . BMiddle $ newMemAssign

cpPreRwMiddle _ _ = const $ return Nothing
