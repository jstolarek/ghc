{-# LANGUAGE GADTs #-}
module CmmCopyPropagation (
   cmmCopyPropagation
 ) where

import Cmm
import CmmUtils
import DynFlags
import Hoopl
import UniqSupply

import Control.Applicative
import Control.Arrow      as CA
import qualified Data.Map as M
import Data.Maybe

import System.IO.Unsafe

-- I'm not sure about []. Perhaps I should pass sth?
cmmCopyPropagation :: DynFlags -> CmmGraph -> UniqSM CmmGraph
cmmCopyPropagation dflags graph = do
     g' <- dataflowPassFwd graph [] $ analRewFwd cpLattice cpTransfer (cpRewrite dflags)
     return . fst $ g'

-- plural and singular names (Facts vs. Fact) are confusing
type RegLocation         = CmmReg
type MemLocation         = (Area, Int)
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

-- I think that here I don't need to use gen and kill sets, because at any given
-- time there is at most one fact about assignment to any given location. If we
-- are assigning to a location which is already in the list of facts, the old
-- fact will be replaced by the new one

cpTransferMiddle :: CmmNode O O -> CopyPropagationFact -> CopyPropagationFact

-- _regA::T = 7
cpTransferMiddle (CmmAssign lhs rhs@(CmmLit _)) =
    addRegFact lhs rhs
-- _regA::T = _regB::T
cpTransferMiddle (CmmAssign lhs rhs@(CmmReg _)) =
    addRegFact lhs rhs
-- T[(old + 8)] = 7
cpTransferMiddle (CmmStore (CmmStackSlot lhs off) rhs@(CmmLit _)) =
    addMemFact (lhs, off) rhs
-- T[(old + 8)] = _regA::T
cpTransferMiddle (CmmStore (CmmStackSlot lhs off) rhs@(CmmReg _)) =
    addMemFact (lhs, off) rhs
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

cpRewrite :: DynFlags -> FwdRewrite UniqSM CmmNode CopyPropagationFact
cpRewrite dflags = deepFwdRw3 cpRwFirst (cpRwMiddle dflags) cpRwLast
    where cpRwFirst _ _ = return Nothing

cpRwMiddle :: DynFlags
           -> CmmNode O O
           -> CopyPropagationFact
           -> UniqSM (Maybe (Graph CmmNode O O))

-- R2 = R1         ======>    R2 = R1
-- I32[old] = R2              I32[old] = R1
cpRwMiddle _ (CmmStore lhs (CmmReg rhs)) (_, Info regFact) =
    return $ (GUnit . BMiddle . CmmStore lhs) `fmap` M.lookup rhs regFact

-- I32[old] = R1              ====>  I32[old] = R1
-- I32[old + 4] = I32[old]           I32[old + 4] = R1
cpRwMiddle _ (CmmStore lhs (CmmStackSlot reg off)) (Info memFact, _) =
    return $ (GUnit . BMiddle . CmmStore lhs) `fmap` M.lookup (reg, off) memFact

-- I32[Sp] = 7    ====> I32[Sp]
cpRwMiddle _ (CmmStore _ (CmmLit _)) _ = return Nothing

--  I32[Sp] = expr  ====> Rx = expr
--                        I32[Sp] = Rx
cpRwMiddle dflags (CmmStore lhs rhs) _ = do
  u <- getUniqueUs
  let regSize      = cmmExprType dflags rhs
      newReg       = CmmLocal $ LocalReg u regSize
      newRegAssign = CmmAssign newReg rhs
      newMemAssign = CmmStore lhs (CmmReg newReg)
  return . Just . GUnit . BCons newRegAssign . BMiddle $ newMemAssign

-- R2 = R1    =====>    R2 = R1
-- R3 = R2              R3 = R1
cpRwMiddle _ (CmmAssign lhs (CmmReg rhs)) (_, Info regFact) =
    return $ (GUnit . BMiddle . CmmAssign lhs) <$> M.lookup rhs regFact -- is this comprehensible?

-- I32[Sp] = expr  =====> I32[Sp] = expr
-- R1 = I32[Sp]           R1 = expr
cpRwMiddle _ (CmmAssign lhs (CmmLoad (CmmStackSlot reg off) _)) (Info memFact, _) =
    return $ (GUnit . BMiddle . CmmAssign lhs) <$> M.lookup (reg, off) memFact

cpRwMiddle _ (CmmAssign lhs rhs) facts = return $ GUnit . BMiddle . CmmAssign lhs <$> cmmRwExpr rhs facts

{- This one is a nightmare -}
cpRwMiddle _ (CmmUnsafeForeignCall tgt res args) facts@(_, regFacts) =
    if isSomeChange [f1, f2, f3]
    then return . Just . GUnit . BMiddle . CmmUnsafeForeignCall tgt' res' $ args'
    else return Nothing
        where
          (f1, tgt')  = rwForeignCallTarget facts    tgt
          (f2, res')  = rwResults           regFacts res
          (f3, args') = rwActual            facts    args

cpRwMiddle _ _ _ = return Nothing

rwForeignCallTarget :: CopyPropagationFact -> ForeignTarget -> (ChangeFlag, ForeignTarget)
rwForeignCallTarget facts (ForeignTarget expr conv) =
    (\e -> ForeignTarget e conv) <$> cmmMaybeRwWithDefault expr (flip cmmRwExpr $ facts)
rwForeignCallTarget _ target = (NoChange, target)

-- results or formal args?
rwResults :: RegAssignmentFacts -> [CmmFormal] -> (ChangeFlag, [CmmFormal])
rwResults regFacts results =
    case cmmRwRegs (wrapLocalReg results) regFacts of
      Nothing  -> (NoChange  , results           )
      Just res -> (SomeChange, unwrapCmmLocal res)
    where
      wrapLocalReg = map CmmLocal
      unwrapCmmLocal []                    = []
      unwrapCmmLocal (CmmLocal reg : regs) = reg : unwrapCmmLocal regs
      unwrapCmmLocal (_            : regs) =       unwrapCmmLocal regs

-- actual or arguments?
rwActual :: CopyPropagationFact -> [CmmActual] -> (ChangeFlag, [CmmActual])
rwActual facts arguments =
    cmmMaybeRwWithDefault arguments (flip cmmRwExprs $ facts)

cmmMaybeRwWithDefault :: a -> (a -> Maybe a) -> (ChangeFlag, a)
cmmMaybeRwWithDefault def f =
    case f def of
      Nothing  -> (NoChange  , def)
      Just res -> (SomeChange, res)

cpRwLast :: CmmNode O C
         -> CopyPropagationFact
         -> UniqSM (Maybe (Graph CmmNode O C))
cpRwLast (CmmCondBranch pred t f) facts = return $ gUnitOC . (BlockOC BNil) . (\p -> CmmCondBranch p t f) <$> cmmRwExpr pred facts
cpRwLast (CmmSwitch scrut labels) facts = return $ gUnitOC . (BlockOC BNil) . (\s -> CmmSwitch s labels) <$> cmmRwExpr scrut facts
cpRwLast call@(CmmCall { cml_target = target }) facts = return $ gUnitOC . (BlockOC BNil) . (\t -> call {cml_target = t}) <$> cmmRwExpr target facts
cpRwLast (CmmForeignCall tgt res args succ updfr intrbl) facts@(_, regFacts) =
    if isSomeChange [f1, f2, f3]
    then return . Just . gUnitOC . (BlockOC BNil) . CmmForeignCall tgt' res' args' succ updfr $ intrbl
    else return Nothing
        where
          (f1, tgt')  = rwForeignCallTarget facts    tgt
          (f2, res')  = rwResults           regFacts res
          (f3, args') = rwActual            facts    args

cpRwLast _ _ = return Nothing

-- move to some utility module!
isSomeChange :: [ChangeFlag] -> Bool
isSomeChange []                = False
isSomeChange (SomeChange : xs) = True
isSomeChange (_          : xs) = isSomeChange xs


cmmRwExpr :: CmmExpr -> CopyPropagationFact -> Maybe CmmExpr
cmmRwExpr (CmmLoad expr ty) facts = (\e -> CmmLoad e ty) <$> cmmRwExpr expr facts
cmmRwExpr (CmmReg reg) (_, Info regFact) = M.lookup reg regFact
cmmRwExpr (CmmMachOp machOp params) facts = CmmMachOp machOp <$> cmmRwExprs params facts
cmmRwExpr (CmmStackSlot area off) (Info facts, _) = M.lookup (area, off) facts
cmmRwExpr (CmmRegOff reg off) (_, facts) =
    (\r -> CmmRegOff r off) <$> cmmRwReg reg facts
cmmRwExpr _ _ = Nothing

cmmRwReg :: CmmReg -> RegAssignmentFacts -> Maybe CmmReg
cmmRwReg reg (Info fact) =  -- pattern matching within a loop, would be good to float outside
    case M.lookup reg fact of
      Just (CmmReg reg') -> Just reg'
      _                  -> Nothing
cmmRwReg _ _ = Nothing

cmmRwExprs :: [CmmExpr] -> CopyPropagationFact -> Maybe [CmmExpr]
cmmRwExprs = cmmRwList cmmRwExpr

cmmRwRegs :: [CmmReg] -> RegAssignmentFacts -> Maybe [CmmReg]
cmmRwRegs = cmmRwList cmmRwReg

cmmRwList :: (a -> f -> Maybe a) -> [a] -> f -> Maybe [a]
cmmRwList f xs facts =
    case foldr rw (NoChange, []) xs of
      (NoChange  , _  ) -> Nothing
      (SomeChange, xs') -> Just xs'
    where rw x (flag, xs) =
              case f x facts of
                Nothing -> (flag      , x : xs)
                Just x' -> (SomeChange, x': xs)
