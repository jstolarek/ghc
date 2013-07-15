{-# LANGUAGE GADTs #-}
module CmmCopyPropagation (
   cmmCopyPropagation
 ) where

import Cmm
import CmmUtils
import DynFlags
import Hoopl
import UniqSupply

import Control.Arrow      as CA
import qualified Data.Map as M

-- I'm not sure about []. Perhaps I should pass sth?
cmmCopyPropagation :: DynFlags -> CmmGraph -> UniqSM CmmGraph
cmmCopyPropagation dflags graph = do
     g' <- dataflowPassFwd graph [] $ analRewFwd cpLattice cpTransfer (cpRewrite dflags)
     return . fst $ g'

type RegLocation         = CmmReg
type MemLocation         = (CmmReg, Int)
type CmmFactValue        = CmmExpr
-- Bottom - we know nothing, we have not yet analyzed this part of the graph
-- Info - hey, we know sth! If element is in the map we know its value. If it
--        is not then we know we now nothing (Top!)
data AssignmentFacts a   = Bottom
                         | Info (M.Map a CmmExpr)
type RegAssignmentFacts  = AssignmentFacts RegLocation
type MemAssignmentFacts  = AssignmentFacts MemLocation
type CopyPropagationFact = (MemAssignmentFacts, RegAssignmentFacts)

--todo: use cmmMachOpFold from CmmOpt to do constant folding after rewriting

cpLattice :: DataflowLattice CopyPropagationFact
cpLattice = DataflowLattice "copy propagation" (Bottom, Bottom) cpJoin

cpJoin :: JoinFun CopyPropagationFact
cpJoin _ (OldFact (oldMem, oldReg)) (NewFact (newMem, newReg)) =
              (chFlag, (joinMem, joinReg))
    where (memChange, joinMem) = intersectFacts oldMem newMem
          (regChange, joinReg) = intersectFacts oldReg newReg
          chFlag = case memChange of
                     SomeChange -> SomeChange
                     _          -> case regChange of
                                     SomeChange -> SomeChange
                                     _          -> NoChange

intersectFacts :: Ord v
               => AssignmentFacts v
               -> AssignmentFacts v
               -> (ChangeFlag, AssignmentFacts v)
intersectFacts facts  Bottom         = (NoChange  ,      facts)  -- really NoChange?
intersectFacts Bottom facts          = (SomeChange,      facts)
intersectFacts (Info old) (Info new) = (flag      , Info facts)
  where
    (flag, facts) = M.foldrWithKey add (NoChange, M.empty) new
    add k new_v (ch, joinmap) =
      case M.lookup k old of
        Nothing    -> (SomeChange, joinmap)
        Just old_v -> if old_v == new_v
                      then (ch, M.insert k new_v joinmap)
                      else (SomeChange, joinmap)

cpTransfer :: FwdTransfer CmmNode CopyPropagationFact
cpTransfer = mkFTransfer3 cpTransferFirst cpTransferMiddle cpTransferLast

cpTransferFirst :: CmmNode C O -> CopyPropagationFact -> CopyPropagationFact
cpTransferFirst _ fact = fact

-- For now I'm supposed to only focus on simple assignments that contain a register
-- or a memory location. This is probably the place to do it by limiting pattern
-- matching on rhs. I'm not yet sure on what I should pattern match.
-- CmmReg and CmmLit maybe?
--
-- I think that here I don't need to use gen and kill sets, because at any given
-- time there is at most one fact about assignment to any given location. If we
-- are assigning to a location which is already in the list of facts, the old
-- fact will be replaced by the new one

-- lets just focus on assignments to registers. CmmLit will deal with literals,
-- CmmReg will deal with registers. I'm y
cpTransferMiddle :: CmmNode O O -> CopyPropagationFact -> CopyPropagationFact

cpTransferMiddle (CmmAssign lhs rhs@(CmmLit _)) =
    addRegFact lhs rhs
cpTransferMiddle (CmmAssign lhs rhs@(CmmReg _)) =
    addRegFact lhs rhs
cpTransferMiddle (CmmStore (CmmRegOff lhs off) rhs@(CmmLit _)) =
    addMemFact (lhs, off) rhs
cpTransferMiddle (CmmStore (CmmRegOff lhs off) rhs@(CmmReg _)) =
    addMemFact (lhs, off) rhs
--cpTransferMiddle (CmmStore (CmmLoad lhs off) rhs@(CmmReg _)) =
--    addMemFact (lhs, off) rhs
cpTransferMiddle _ = id

addMemFact :: MemLocation -> CmmFactValue -> CopyPropagationFact -> CopyPropagationFact
addMemFact k v = CA.first $ addFact k v

addRegFact :: RegLocation -> CmmFactValue -> CopyPropagationFact -> CopyPropagationFact
addRegFact k v = CA.second $ addFact k v

addFact :: Ord a => a -> CmmFactValue -> AssignmentFacts a -> AssignmentFacts a
addFact k v Bottom       = Info $ M.singleton k v
addFact k v (Info facts) = Info $ M.insert    k v facts

cpTransferLast :: CmmNode O C -> CopyPropagationFact -> FactBase CopyPropagationFact
cpTransferLast = distributeFact

-- why do I need UniqSM monad? Hoopl uses either m or FuelMonad m
cpRewrite :: DynFlags -> FwdRewrite UniqSM CmmNode CopyPropagationFact
cpRewrite dflags = mkFRewrite3 cpRwFirst (cpRewriteMiddle dflags) cpRwLast
    where cpRwFirst _ _ = return Nothing
          cpRwLast  _ _ = return Nothing

cpRewriteMiddle :: DynFlags
                -> CmmNode O O
                -> CopyPropagationFact
                -> UniqSM (Maybe (Graph CmmNode O O))
-- R2 = R1    =====>    R2 = R1
-- R3 = R2              R3 = R1
cpRewriteMiddle _ (CmmAssign lhs (CmmReg rhs)) (_, Info regFact) =
    return $ (GUnit . BMiddle . CmmAssign lhs) `fmap` M.lookup rhs regFact -- is this comprehensible?
-- R2 = R1         ======>    R2 = R1
-- I32[Sp] = R2               I32[Sp] = R1
cpRewriteMiddle _ (CmmStore lhs (CmmReg rhs)) (_, Info regFact) =
    return $ (GUnit . BMiddle . CmmStore lhs) `fmap` M.lookup rhs regFact
-- I32[Sp] = R1              ====>  I32[Sp] = R1
-- I32[Sp + 4] = I32[Sp]            I32[Sp + 4] = R1
cpRewriteMiddle _ (CmmStore lhs (CmmRegOff reg off)) (Info memFact, _) =
    return $ (GUnit . BMiddle . CmmStore lhs) `fmap` M.lookup (reg, off) memFact
-- I32[Sp] = 7    ====> I32[Sp]
cpRewriteMiddle _ (CmmStore _ (CmmLit _)) _ = return Nothing
--  I32[Sp] = expr  ====> Rx = expr
--                        I32[Sp] = Rx
cpRewriteMiddle dflags (CmmStore lhs rhs) _ = do
  u <- getUniqueUs
  let regSize      = cmmExprType dflags rhs
      newReg       = CmmLocal $ LocalReg u regSize
      newRegAssign = CmmAssign newReg rhs
      newMemAssign = CmmStore lhs (CmmReg newReg)
  return . Just . GUnit . BCons newRegAssign . BMiddle $ newMemAssign
-- I32[Sp] = expr  =====> I32[Sp] = expr
-- R1 = I32[Sp]           R1 = expr
cpRewriteMiddle _ (CmmAssign lhs (CmmRegOff reg off)) (Info memFact, _) =
    return $ (GUnit . BMiddle . CmmAssign lhs) `fmap` M.lookup (reg, off) memFact
cpRewriteMiddle _ _ _ = return Nothing

