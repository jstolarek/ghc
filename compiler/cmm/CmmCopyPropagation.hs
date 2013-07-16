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

--todo: use cmmMachOpFold from CmmOpt to do constant folding after rewriting

-- I'm not sure about []. Perhaps I should pass sth?
cmmCopyPropagation :: DynFlags -> CmmGraph -> UniqSM CmmGraph
cmmCopyPropagation dflags graph = do
     g' <- dataflowPassFwd graph [] $ analRewFwd cpLattice cpTransfer (cpRewrite dflags)
     return . fst $ g'

type RegisterLocation  = CmmReg
type StackLocation     = (Area, Int)
type CmmFact           = CmmExpr
data AssignmentFacts a = Bottom  -- ADD NOTE HERE
                       | Info (M.Map a CmmExpr)
type RegisterFacts       = AssignmentFacts RegisterLocation
type StackFacts        = AssignmentFacts StackLocation
type CPFacts           = (StackFacts, RegisterFacts)

-- Bottom - we know nothing, we have not yet analyzed this part of the graph
-- Info - hey, we know sth! If element is in the map we know its value. If it
--        is not then we know we now nothing (Top!)

cpLattice :: DataflowLattice CPFacts
cpLattice = DataflowLattice "copy propagation" (Bottom, Bottom) cpJoin

cpJoin :: JoinFun CPFacts
cpJoin _ (OldFact (oldMem, oldReg)) (NewFact (newMem, newReg)) =
              (changeFlag, (joinMem, joinReg))
    where (memChange, joinMem) = intersectFacts oldMem newMem
          (regChange, joinReg) = intersectFacts oldReg newReg
          changeFlag           = sumChanges [memChange, regChange]

cpTransfer :: FwdTransfer CmmNode CPFacts
cpTransfer = mkFTransfer3 cpTransferFirst cpTransferMiddle distributeFact
    where cpTransferFirst _ fact = fact

-- utility functions for lattice definition

intersectFacts :: Ord v
               => AssignmentFacts v
               -> AssignmentFacts v
               -> (ChangeFlag, AssignmentFacts v)
intersectFacts facts  Bottom         = (NoChange  ,      facts)
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

-- I think that here I don't need to use gen and kill sets, because at any given
-- time there is at most one fact about assignment to any given location. If we
-- are assigning to a location which is already in the list of facts, the old
-- fact will be replaced by the new one

cpTransferMiddle :: CmmNode O O -> CPFacts -> CPFacts

-- _regA::T = 7
cpTransferMiddle (CmmAssign lhs rhs@(CmmLit _)) =
    addRegisterFact lhs rhs
-- _regA::T = _regB::T
cpTransferMiddle (CmmAssign lhs rhs@(CmmReg _)) =
    addRegisterFact lhs rhs
-- T[(old + 8)] = 7
cpTransferMiddle (CmmStore (CmmStackSlot lhs off) rhs@(CmmLit _)) =
    addStackFact (lhs, off) rhs
-- T[(old + 8)] = _regA::T
cpTransferMiddle (CmmStore (CmmStackSlot lhs off) rhs@(CmmReg _)) =
    addStackFact (lhs, off) rhs
cpTransferMiddle _ = id


-- utility functions for transfer functions

addStackFact :: StackLocation -> CmmFact -> CPFacts -> CPFacts
addStackFact k v = CA.first $ addFact k v

addRegisterFact :: RegisterLocation -> CmmFact -> CPFacts -> CPFacts
addRegisterFact k v = CA.second $ addFact k v

addFact :: Ord a => a -> CmmFact -> AssignmentFacts a -> AssignmentFacts a
addFact k v Bottom       = Info $ M.singleton k v
addFact k v (Info facts) = Info $ M.insert    k v facts

lookupStackFact :: StackLocation -> CPFacts -> Maybe CmmFact
lookupStackFact k = lookupAssignmentFact k . fst

lookupRegisterFact :: RegisterLocation -> CPFacts -> Maybe CmmFact
lookupRegisterFact k = lookupAssignmentFact k . snd

lookupAssignmentFact :: Ord a => a -> AssignmentFacts a -> Maybe CmmFact
lookupAssignmentFact _ Bottom       = Nothing
lookupAssignmentFact k (Info facts) = M.lookup k facts

-- rewrite functions

cpRewrite :: DynFlags -> FwdRewrite UniqSM CmmNode CPFacts
cpRewrite dflags = deepFwdRw3 cpRwFirst (cpRwMiddle dflags) cpRwLast
    where cpRwFirst _ _ = return Nothing

cpRwMiddle :: DynFlags
           -> CmmNode O O
           -> CPFacts
           -> UniqSM (Maybe (Graph CmmNode O O))
-- R2 = R1         ======>    R2 = R1
-- I32[old] = R2              I32[old] = R1
cpRwMiddle _ (CmmStore lhs (CmmReg rhs)) =
    rwCmmExprToGraphOO (lookupRegisterFact rhs) (CmmStore lhs)

-- I32[old] = R1              ====>  I32[old] = R1
-- I32[old + 4] = I32[old]           I32[old + 4] = R1
cpRwMiddle _ (CmmStore lhs (CmmStackSlot reg off)) =
    rwCmmExprToGraphOO (lookupStackFact (reg, off)) (CmmStore lhs)

-- I32[Sp] = 7    ====> I32[Sp]
cpRwMiddle _ (CmmStore _ (CmmLit _)) = const $ return Nothing

--  I32[Sp] = expr  ====> Rx = expr
--                        I32[Sp] = Rx
cpRwMiddle dflags (CmmStore lhs rhs) = const $ do
  u <- getUniqueUs
  let regSize      = cmmExprType dflags rhs
      newReg       = CmmLocal $ LocalReg u regSize
      newRegAssign = CmmAssign newReg rhs
      newMemAssign = CmmStore lhs (CmmReg newReg)
  return . Just . GUnit . BCons newRegAssign . BMiddle $ newMemAssign

-- R2 = R1    =====>    R2 = R1
-- R3 = R2              R3 = R1
cpRwMiddle _ (CmmAssign lhs (CmmReg rhs)) =
    rwCmmExprToGraphOO (lookupRegisterFact rhs) (CmmAssign lhs)

-- I32[Sp] = expr  =====> I32[Sp] = expr
-- R1 = I32[Sp]           R1 = expr
cpRwMiddle _ (CmmAssign lhs (CmmLoad (CmmStackSlot reg off) _)) =
    rwCmmExprToGraphOO (lookupStackFact (reg, off)) (CmmAssign lhs)

cpRwMiddle _ (CmmAssign lhs rhs) =
    rwCmmExprToGraphOO (cmmRwExpr rhs) (CmmAssign lhs)

cpRwMiddle _ (CmmUnsafeForeignCall tgt res args) =
    rwFunctionCall tgt res args (\t r a ->
      GUnit . BMiddle . CmmUnsafeForeignCall t r $ a)

cpRwMiddle _ _ = const $ return Nothing

cpRwLast :: CmmNode O C
         -> CPFacts
         -> UniqSM (Maybe (Graph CmmNode O C))
cpRwLast      (CmmCondBranch pred  t f        ) = rwCmmExprToGraphOC pred   (\p -> CmmCondBranch p t f  )
cpRwLast      (CmmSwitch     scrut labels     ) = rwCmmExprToGraphOC scrut  (\s -> CmmSwitch s labels   )
cpRwLast call@(CmmCall { cml_target = target }) = rwCmmExprToGraphOC target (\t -> call {cml_target = t})
cpRwLast      (CmmForeignCall tgt res args succ updfr intrbl) =
    rwFunctionCall tgt res args (\t r a ->
      gUnitOC . (BlockOC BNil) . CmmForeignCall t r a succ updfr $ intrbl)
cpRwLast _ = const $ return Nothing

-- rewrite utility functions

rwFunctionCall :: ForeignTarget
               -> [CmmFormal]
               -> [CmmActual]
               -> (ForeignTarget -> [CmmFormal] -> [CmmActual] -> Graph CmmNode e x)
               -> CPFacts
               -> UniqSM (Maybe (Graph CmmNode e x))
rwFunctionCall tgt res args fun facts@(_, regFacts) =
     let (f1, tgt')  = rwForeignCallTarget tgt  facts
         (f2, res')  = rwResults           res  regFacts
         (f3, args') = rwActual            args facts
     in case sumChanges [f1, f2, f3] of
      SomeChange -> return . Just $ (fun tgt' res' args')
      NoChange   -> return Nothing

rwForeignCallTarget :: ForeignTarget
                    -> (CPFacts -> (ChangeFlag, ForeignTarget))
rwForeignCallTarget (ForeignTarget expr conv) =
    fmap (\e -> ForeignTarget e conv) . cmmMaybeRwWithDefault expr . flip cmmRwExpr
rwForeignCallTarget target = const (NoChange, target)

-- results or formal args?
rwResults :: [CmmFormal] -> RegisterFacts -> (ChangeFlag, [CmmFormal])
rwResults results regFacts =
    case cmmRwRegs (wrapLocalReg results) regFacts of
      Nothing  -> (NoChange  , results           )
      Just res -> (SomeChange, unwrapCmmLocal res)
    where
      wrapLocalReg = map CmmLocal
      unwrapCmmLocal []                    = []
      unwrapCmmLocal (CmmLocal reg : regs) = reg : unwrapCmmLocal regs
      unwrapCmmLocal (_            : regs) =       unwrapCmmLocal regs -- add panic here

-- actual or arguments?
rwActual :: [CmmActual] -> CPFacts -> (ChangeFlag, [CmmActual])
rwActual arguments = cmmMaybeRwWithDefault arguments . flip cmmRwExprs

-- takes a function to lookup facts, a function that wraps rewritten
-- expression into a node, a set of facts and maybe returns a rewriten graph
rwCmmExprToGraphOO :: (CPFacts -> Maybe CmmExpr)
                   -> (CmmExpr -> CmmNode O O)
                   -> (CPFacts -> UniqSM (Maybe (Graph CmmNode O O)))
rwCmmExprToGraphOO factLookup exprToNode =
    return . fmap (GUnit . BMiddle . exprToNode) . factLookup

-- this function takes an expression to rewrite, a function that wraps rewritten
-- expression into a node, a set of facts and maybe returns a rewriten graph
rwCmmExprToGraphOC :: CmmExpr
                   -> (CmmExpr -> CmmNode O C)
                   -> (CPFacts -> UniqSM (Maybe (Graph CmmNode O C)))
rwCmmExprToGraphOC expr exprToNode =
    return . fmap (gUnitOC . (BlockOC BNil) . exprToNode) . cmmRwExpr expr

cmmMaybeRwWithDefault :: a -> (a -> Maybe a) -> (ChangeFlag, a)
cmmMaybeRwWithDefault def f =
    case f def of
      Nothing  -> (NoChange  , def)
      Just res -> (SomeChange, res)

cmmRwExpr :: CmmExpr -> CPFacts -> Maybe CmmExpr
cmmRwExpr (CmmReg reg             ) = lookupRegisterFact reg
cmmRwExpr (CmmStackSlot area off  ) = lookupStackFact (area, off)
cmmRwExpr (CmmMachOp machOp params) = fmap (CmmMachOp machOp) . cmmRwExprs params
cmmRwExpr (CmmLoad expr ty        ) = fmap (\e -> CmmLoad e ty) . cmmRwExpr expr
cmmRwExpr (CmmRegOff reg off      ) = fmap (\r -> CmmRegOff r off) . cmmRwReg reg . snd
cmmRwExpr _                         = const Nothing

cmmRwReg :: CmmReg -> RegisterFacts -> Maybe CmmReg
cmmRwReg reg (Info fact) =
    case M.lookup reg fact of
      Just (CmmReg reg') -> Just reg'
      _                  -> Nothing
cmmRwReg _ _ = Nothing

cmmRwExprs :: [CmmExpr] -> CPFacts -> Maybe [CmmExpr]
cmmRwExprs = cmmRwList cmmRwExpr

cmmRwRegs :: [CmmReg] -> RegisterFacts -> Maybe [CmmReg]
cmmRwRegs = cmmRwList cmmRwReg

cmmRwList :: (a -> f -> Maybe a) -> [a] -> f -> Maybe [a]
cmmRwList f xs facts =
    case foldr rw (NoChange, []) xs of
      (NoChange  , _  ) -> Nothing
      (SomeChange, xs') -> Just xs'
    where
      rw x (flag, xs) =
          case f x facts of
            Nothing -> (flag      , x : xs)
            Just x' -> (SomeChange, x': xs)

-- other utility functions. This should probably go in some utility module
sumChanges :: [ChangeFlag] -> ChangeFlag
sumChanges []                = NoChange
sumChanges (SomeChange : _ ) = SomeChange
sumChanges (_          : xs) = sumChanges xs
