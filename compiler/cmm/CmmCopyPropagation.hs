module CmmCopyPropagation where

import Cmm
import qualified Data.Map as M
import Hoopl
import UniqSupply

cmmCopyPropagation :: CmmGraph -> CmmGraph
cmmCopyPropagation g = g

type CopyPropagationFact = (M.Map (CmmReg, Int) CmmExpr, M.Map CmmReg CmmExpr)

--todo: use cmmMachOpFold from CmmOpt to do constant folding after rewriting

cpFwdPass :: FwdPass UniqSM CmmNode CopyPropagationFact
cpFwdPass = FwdPass cpLattice cpTransfer cpRewrite

cpLattice :: DataflowLattice CopyPropagationFact
cpLattice = DataflowLattice "copy propagation" cpBottom cpJoin

cpBottom :: CopyPropagationFact
cpBottom = (M.empty, M.empty)

--type JoinFun a = Label -> OldFact a -> NewFact a -> (ChangeFlag, a)
-- what is a label?
cpJoin :: JoinFun CopyPropagationFact
cpJoin _ oldFact newFact = undefined

cpTransfer :: FwdTransfer CmmNode CopyPropagationFact
cpTransfer = mkFTransfer3 cpTransferFirst cpTransferMiddle cpTransferLast

cpTransferFirst :: CmmNode C O -> CopyPropagationFact -> CopyPropagationFact
cpTransferFirst node fact = undefined

cpTransferMiddle :: CmmNode O O -> CopyPropagationFact -> CopyPropagationFact
cpTransferMiddle node fact = undefined

cpTransferLast :: CmmNode O C -> CopyPropagationFact -> FactBase CopyPropagationFact
cpTransferLast node fact = undefined

-- why do I need UniqSM monad? Hoopl uses either m or FuelMonad m
cpRewrite :: FwdRewrite UniqSM CmmNode CopyPropagationFact
cpRewrite = mkFRewrite3 cpRewriteFirst cpRewriteMiddle cpRewriteLast

cpRewriteFirst :: CmmNode C O
               -> CopyPropagationFact
               -> m (Maybe (Graph CmmNode C O))
cpRewriteFirst node fact = undefined

cpRewriteMiddle :: CmmNode O O
                -> CopyPropagationFact
                -> m (Maybe (Graph CmmNode O O))
cpRewriteMiddle node fact = undefined

cpRewriteLast :: CmmNode O C
              -> CopyPropagationFact
              -> m (Maybe (Graph CmmNode O C))
cpRewriteLast node fact = undefined
