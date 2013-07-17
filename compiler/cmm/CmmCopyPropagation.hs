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

-- A TODO and FIXME list for this module:
--  * use cmmMachOpFold from CmmOpt to do constant folding after rewriting
--  * I'm not sure about passing [] to dataFlowPassFwd. Perhaps I should pass
--    something else?
--  * there is some naming confusion with fields of function calls. One of
--    the fields is called `actual` but the comment mentions these are the
--    arguments. Which name is better to use? related: rwActual and some notes
--    There is a similar problem witg results vs. formals (see rwResults).
--    related: [Rewriting function calls]
--  * last equation of unwrapCmmLocal should cause compiler panic, because
--    it should never be reached
--  * move sumChanges to some utility module

-----------------------------------------------------------------------------
--                           Copy propagation pass
-----------------------------------------------------------------------------

cmmCopyPropagation :: DynFlags -> CmmGraph -> UniqSM CmmGraph
cmmCopyPropagation dflags graph = do
     g' <- dataflowPassFwd graph [] $ analRewFwd cpLattice cpTransfer (cpRewrite dflags)
     return . fst $ g'

-----------------------------------------------------------------------------
--                        Data types used as facts
-----------------------------------------------------------------------------

type RegisterLocation  = CmmReg
type StackLocation     = (Area, Int)
type CmmFact           = CmmExpr
data AssignmentFacts a = Bottom  -- See Note [Assignment facts lattice]
                       | Info (M.Map a CmmExpr)
type RegisterFacts     = AssignmentFacts RegisterLocation
type StackFacts        = AssignmentFacts StackLocation
type CPFacts           = (StackFacts, RegisterFacts)

-- Note [Copy propagation facts]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- We distinguish two kinds of facts. First are the assignments to registers,
-- which are refered to by a value of CmmReg. Second are the assignments to
-- stack locations, which are represented by a tuple (Area, Int). Since this
-- pass is done before the stack layout, we don't yet have explict global
-- registers like Sp and therefore we operate on stack areas with an offset
-- (these are stored in a CmmStackSlot data constructor). Both types of facts
-- take the same values, namely a CmmExpr to which an assignment can be
-- rewriten. We pass these two sets of facts - RegisterFacts and StackFacts -
-- to most of the functions as a tuple.

-- Note [Assignment facts lattice]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Bottom value constructor represents the bottom element of a dataflow
-- lattice. It is used as an initial value assigned to blocks that have not
-- yet been analyzed. Once we start analyzing a basic block we create a
-- map of assignment facts stored in the Info data constructor. We map from
-- the left hand side of an assignment to its right hand side (see Note
-- [Copy propagation facts]). If an expression is present in the map as a key
-- it means that we know the exact value that this expression can be rewritten
-- to. If an expression is not present in a map it means that we know that
-- this expression can be rewritten. In other words, lack of expression in
-- a map of facts represents top of a lattice.

-----------------------------------------------------------------------------
--                              Lattice
-----------------------------------------------------------------------------

cpLattice :: DataflowLattice CPFacts
cpLattice = DataflowLattice "copy propagation" (Bottom, Bottom) cpJoin

cpJoin :: JoinFun CPFacts
cpJoin _ (OldFact (oldMem, oldReg)) (NewFact (newMem, newReg)) =
              (changeFlag, (joinMem, joinReg))
    where (memChange, joinMem) = intersectFacts oldMem newMem
          (regChange, joinReg) = intersectFacts oldReg newReg
          changeFlag           = sumChanges [memChange, regChange]

-- Note [Join operation for copy propagation]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- To join two sets of facts we have to use set intersection. Consider this
-- dataflow diagram:
--
--                       |
--                       V
--                   +--------+
--              +----| x := 3 |----+
--              |    +--------+    |
--              |                  |
--              V                  |
--         +--------+              |
--         | x := 4 |              |
--         +--------+              |
--              |                  |
--              |    +--------+    |
--              +--->| x := ? |<---+
--                   +--------+
--                        |
--                        V
--
-- In the left branch we know that x is 4 an in the right one we know it is 3.
-- This means that in the lowest block we are not allowed to rewrite x to any
-- value. We must denote that fact by marking value of x as Top. We do that
-- by removing entry about x from the set of facts (see Note [Assignment facts
-- lattice]). A special case is joining with Bottom. Whenever we join a set of
-- facts with Bottom we return that set as a result.

-----------------------------------------------------------------------------
--                          Transfer function
-----------------------------------------------------------------------------

cpTransfer :: FwdTransfer CmmNode CPFacts
cpTransfer = mkFTransfer3 cpTransferFirst cpTransferMiddle distributeFact
    where cpTransferFirst _ fact = fact

-- Note [Transfer function]
-- ~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Transfer function is responsible for adding new facts to our set of facts.
-- We are only interested in facts about assignments:
--  * of a register or literal to a register. These facts result from the
--    appearence of CmmAssign nodes in the Cmm graph.
--  * of a register or literal to a stack slot. These facts result from the
--    appearence of CmmStore nodes in the Cmm graph.
-- These facts appear only in nodes that are open on entry and exit (see
-- Hoopl paper if you don't understand what this means). In other words
-- assignments don't appear in labels (entry nodes) and jumps, branches and
-- function calls (exit nodes).

cpTransferMiddle :: CmmNode O O -> CPFacts -> CPFacts
cpTransferMiddle (CmmAssign lhs rhs@(CmmLit _)) =
    addRegisterFact lhs rhs
cpTransferMiddle (CmmAssign lhs rhs@(CmmReg _)) =  -- HERE!
    addRegisterFact lhs rhs
cpTransferMiddle _ = id
{-
cpTransferMiddle (CmmStore (CmmStackSlot lhs off) rhs@(CmmLit _)) =
    addStackFact (lhs, off) rhs
cpTransferMiddle (CmmStore (CmmStackSlot lhs off) rhs@(CmmReg _)) =
    addStackFact (lhs, off) rhs
-}
-----------------------------------------------------------------------------
--             Utility functions for adding and finding facts
-----------------------------------------------------------------------------

-- Note [Adding new facts]
-- ~~~~~~~~~~~~~~~~~~~~~~~~
--
-- We add new facts by inserting values into the map. In this way old values
-- (old facts) are simply replaced by new ones. `first` and `second` functions
-- are taken from Control.Arrows and help to avoid boilerplate related to
-- handling values inside a tuple (remember that CPFacts is a tuple).
addStackFact :: StackLocation -> CmmFact -> CPFacts -> CPFacts
addStackFact k v = CA.first $ addFact k v

addRegisterFact :: RegisterLocation -> CmmFact -> CPFacts -> CPFacts
--addRegisterFact k v = CA.second $ addFact k v
addRegisterFact k v (m, fact) = (m, addFact k v fact)

addFact :: Ord a => a -> CmmFact -> AssignmentFacts a -> AssignmentFacts a
addFact k v Bottom       = Info $ M.singleton k v
addFact k v (Info facts) = Info $ M.insert    k v facts

{-
lookupStackFact :: StackLocation -> CPFacts -> Maybe CmmFact
lookupStackFact k = lookupAssignmentFact k . fst

lookupRegisterFact :: RegisterLocation -> CPFacts -> Maybe CmmFact
lookupRegisterFact k = lookupAssignmentFact k . snd

lookupAssignmentFact :: Ord a => a -> AssignmentFacts a -> Maybe CmmFact
lookupAssignmentFact _ Bottom       = Nothing
lookupAssignmentFact k (Info facts) = M.lookup k facts
-}
-- See Note [Join operation for copy propagation]
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

-----------------------------------------------------------------------------
--                     Node rewriting functions
-----------------------------------------------------------------------------

cpRewrite :: DynFlags -> FwdRewrite UniqSM CmmNode CPFacts
cpRewrite dflags = deepFwdRw3 cpRwFirst (cpRwMiddle dflags) cpRwLast
    where cpRwFirst _ _ = return Nothing

-- Note [Rewrite functions]
-- ~~~~~~~~~~~~~~~~~~~~~~~~
--
-- The cpRwMiddle and cpRwLast functions are responsible for doing the graph
-- rewriting. The description of rewriting rules fiven below uses the following
-- notation:
--   * `reg1` and `reg` denote abstract Cmm registers (which may be mapped to
--     hardware registers or spilled)
--   * `I32[(old + 8)]` denotes a location on the stack. I32 represents size of
--     of stored entries (this will be I64 on x86_64), old represents Old stack
--     are (see Note [Copy propagation facts] and Note [Old Area] in CmmExpr.hs)
--   * `expr` denotes a complex expression (that is not a reference to register
--     or stack location)
--
-- The subsequent cpRwMiddle equations do the following:
--
--   1) Rewrite reference to a register with a reference to another register:
--
--      reg2           = reg1            ====> reg2           = reg1
--      I32[(old + 8)] = reg2                  I32[(old + 8)] = reg1
--
--   2) Rewrite reference to a stack area with a reference to a register:
--
--      I32[(old + 8)] = reg1            ====> I32[(old + 8)] = reg1
--      I32[(old + 4)] = I32[(old + 8)]        I32[(old + 4)] = reg1
--
--   3) Assignments of literals to stack areas are not changed:
--
--      I32[(old + 8)] = 7               ====> I32[(old + 8)] = 7
--
--   4) If a complex expression (not a register or literal) is assigned to a
--      stack area we replace it with two instructions: assigning expression
--      to newly allocated register and assigning that register to a stack area.
--      The motivation is to make the stack area dead. Complex expression might
--      be later rewritten recursively.
--
--      I32[(old + 8)] = expr            ====> reg1           = expr
--                                             I32[(old + 8)] = reg1
--
--   5) Same as 1), but when assigned to a register (not a stack area):
--
--      reg2 = reg1                      =====>    reg2 = reg1
--      reg3 = reg2                                reg3 = reg1
--
--   6) Same as 2), but when stack are is assigned an arbitrary expression
--
--     I32[(old + 8)] = reg1             =====> I32[(old + 8)] = reg1
--     reg2           = I32[(old + 8)]          reg2           = reg1
--
--   7) Recursive rewriting of a complex expression assigned to a register:
--
--      reg1 = expr1                     =====> reg1 = expr2
--
--   8) Rewriting of unsafe foreign call parameters
--
--   9) Don't rewrite anything else.
--
-- The subsequent cpRwLast equations recursively rewrite:
--
--   1) predicate of a conditional
--
--   2) scrutinee of a switch
--
--   3) target of a call
--
--   4) target, results and arguments of a foreign call
--
-- Again, last equation prevents rewriting of anything else.
--
-- Rewrite functions make heavy use of helper functions to reduce boilerplate
-- code - see comment for a particular function for a more detailed explanation.

cpRwMiddle :: DynFlags
           -> CmmNode O O
           -> CPFacts
           -> UniqSM (Maybe (Graph CmmNode O O))
cpRwMiddle _ _ = const $ return Nothing
{-cpRwMiddle _ (CmmStore lhs (CmmReg rhs)) =
    rwCmmExprToGraphOO (lookupRegisterFact rhs) (CmmStore lhs)

cpRwMiddle _ (CmmStore lhs (CmmStackSlot reg off)) =
    rwCmmExprToGraphOO (lookupStackFact (reg, off)) (CmmStore lhs)

cpRwMiddle _ (CmmStore _ (CmmLit _)) = const $ return Nothing

cpRwMiddle dflags (CmmStore lhs rhs) = const $ do
  u <- getUniqueUs
  let regSize      = cmmExprType dflags rhs
      newReg       = CmmLocal $ LocalReg u regSize
      newRegAssign = CmmAssign newReg rhs
      newMemAssign = CmmStore lhs (CmmReg newReg)
  return . Just . GUnit . BCons newRegAssign . BMiddle $ newMemAssign

cpRwMiddle _ (CmmAssign lhs (CmmReg rhs)) =
    rwCmmExprToGraphOO (lookupRegisterFact rhs) (CmmAssign lhs)

cpRwMiddle _ (CmmAssign lhs (CmmLoad (CmmStackSlot reg off) _)) =
    rwCmmExprToGraphOO (lookupStackFact (reg, off)) (CmmAssign lhs)

cpRwMiddle _ (CmmAssign lhs rhs) =
    rwCmmExprToGraphOO (rwCmmExpr rhs) (CmmAssign lhs)

cpRwMiddle _ (CmmUnsafeForeignCall tgt res args) =
    rwForeignCall tgt res args (\t r a ->
      GUnit . BMiddle . CmmUnsafeForeignCall t r $ a)
-}

cpRwLast :: CmmNode O C
         -> CPFacts
         -> UniqSM (Maybe (Graph CmmNode O C))
cpRwLast _ = const $ return Nothing
{-cpRwLast      (CmmCondBranch pred  t f        ) =
    rwCmmExprToGraphOC pred   (\p -> CmmCondBranch p t f  )
cpRwLast      (CmmSwitch     scrut labels     ) =
    rwCmmExprToGraphOC scrut  (\s -> CmmSwitch s labels   )
cpRwLast call@(CmmCall { cml_target = target }) =
    rwCmmExprToGraphOC target (\t -> call {cml_target = t})
cpRwLast      (CmmForeignCall tgt res args succ updfr intrbl) =
    rwForeignCall tgt res args (\t r a ->
      gUnitOC . (BlockOC BNil) . CmmForeignCall t r a succ updfr $ intrbl)

-----------------------------------------------------------------------------
--                 Utility functions for node rewriting
-----------------------------------------------------------------------------

-- Note [Rewriting foreign function calls]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Rewriting a foreign call is a bit complex. There are potentially three
-- fields of a call that we might want to rewrite (because they contain CmmExpr,
-- which can be rewritten): target, results list and arguments list. We have to
-- attempt to rewrite every of these three fields and if at least one of them is
-- modified we must rewrite whole function call.
--
-- Helper function rwForeignCall is used when rewriting a CmmUnsafeForeignCall
-- (see cpRwMiddle) and CmmForeignCall (see cpRwLast). It relies on three helper
-- functions: rwForeignCallTarget, rwForeignCallResults and rwForeignCallActual.
-- Each of these functions rewrites a possibly rewritten component of a call
-- and a ChangeFlag which indicated whether the returned value is the original
-- one (NoChange) or a rewritten one (SomeChange). rwForeignCall inspects these
-- three flags and if at least one of them is SomeChange it returns Just a
-- rewritten call. Fourth parameter of rwForeignCall is a function that
-- knows how to construct a rewritten graph from rewritten call parameters.

rwForeignCall :: ForeignTarget
              -> [CmmFormal]
              -> [CmmActual]
              -> (ForeignTarget -> [CmmFormal] -> [CmmActual] -> Graph CmmNode e x)
              -> CPFacts
              -> UniqSM (Maybe (Graph CmmNode e x))
rwForeignCall tgt res args fun facts@(_, regFacts) =
     let (f1, tgt')  = rwForeignCallTarget  tgt  facts
         (f2, res')  = rwForeignCallResults res  regFacts
         (f3, args') = rwForeignCallActual  args facts
     in case sumChanges [f1, f2, f3] of
      SomeChange -> return . Just $ (fun tgt' res' args')
      NoChange   -> return Nothing

rwForeignCallTarget :: ForeignTarget
                    -> (CPFacts -> (ChangeFlag, ForeignTarget))
rwForeignCallTarget (ForeignTarget expr conv) =
    fmap (\e -> ForeignTarget e conv) . maybeRwWithDefault expr . flip rwCmmExpr
rwForeignCallTarget target = const (NoChange, target)

rwForeignCallResults :: [CmmFormal] -> RegisterFacts -> (ChangeFlag, [CmmFormal])
rwForeignCallResults results regFacts =
    case rwCmmRegs (wrapLocalReg results) regFacts of
      Nothing  -> (NoChange  , results           )
      Just res -> (SomeChange, unwrapCmmLocal res)
    where
      wrapLocalReg = map CmmLocal
      unwrapCmmLocal []                    = []
      unwrapCmmLocal (CmmLocal reg : regs) = reg : unwrapCmmLocal regs
      unwrapCmmLocal (_            : regs) =       unwrapCmmLocal regs

rwForeignCallActual :: [CmmActual] -> CPFacts -> (ChangeFlag, [CmmActual])
rwForeignCallActual arguments = maybeRwWithDefault arguments . flip rwCmmExprs

maybeRwWithDefault :: a -> (a -> Maybe a) -> (ChangeFlag, a)
maybeRwWithDefault def f =
    case f def of
      Nothing  -> (NoChange  , def)
      Just res -> (SomeChange, res)

-- rwCmmExprToGraphOO function takes two functions as parameters:
--   * first function takes CPFacts and maybe rewrites a node based on
--     those facts
--   * second function that knows how to convert a rewritten expression
--     into a CmmNode
-- rwCmmExprToGraphOO returns a function that accepts CPFacts and maybe
-- returns a rewritten graph. This function is heavily used by cpRwMiddle.
rwCmmExprToGraphOO :: (CPFacts -> Maybe CmmExpr)
                   -> (CmmExpr -> CmmNode O O)
                   -> (CPFacts -> UniqSM (Maybe (Graph CmmNode O O)))
rwCmmExprToGraphOO factLookup exprToNode =
    return . fmap (GUnit . BMiddle . exprToNode) . factLookup

-- rwCmmExprToGraphOC function takes two parameters:
--   * expression to rewrite
--   * function that knows how to convert a rewritten expression into a CmmNode
-- rwCmmExprToGraphOC returns a function that accepts CPFacts and maybe
-- returns a rewritten graph. This function is heavily used by cpRwLast.
rwCmmExprToGraphOC :: CmmExpr
                   -> (CmmExpr -> CmmNode O C)
                   -> (CPFacts -> UniqSM (Maybe (Graph CmmNode O C)))
rwCmmExprToGraphOC expr exprToNode =
    return . fmap (gUnitOC . (BlockOC BNil) . exprToNode) . rwCmmExpr expr

-- rwCmmExpr takes a Cmm expression and a set of facts and attempts to
-- recursively rewrite that expression. First two equations attempt to
-- rewrite based on facts about a register of a stack area. Remaining
-- equations recurse on Cmm expressions stored within other data
-- constructors.
rwCmmExpr :: CmmExpr -> CPFacts -> Maybe CmmExpr
rwCmmExpr (CmmReg reg             ) = lookupRegisterFact reg
rwCmmExpr (CmmStackSlot area off  ) = lookupStackFact (area, off)
rwCmmExpr (CmmMachOp machOp params) = fmap (CmmMachOp machOp) . rwCmmExprs params
rwCmmExpr (CmmLoad expr ty        ) = fmap (\e -> CmmLoad e ty) . rwCmmExpr expr
rwCmmExpr (CmmRegOff reg off      ) = fmap (\r -> CmmRegOff r off) . rwCmmReg reg . snd
rwCmmExpr _                         = const Nothing

rwCmmReg :: CmmReg -> RegisterFacts -> Maybe CmmReg
rwCmmReg reg (Info fact) =
    case M.lookup reg fact of
      Just (CmmReg reg') -> Just reg'
      _                  -> Nothing
rwCmmReg _ _ = Nothing

rwCmmExprs :: [CmmExpr] -> CPFacts -> Maybe [CmmExpr]
rwCmmExprs = rwCmmList rwCmmExpr

rwCmmRegs :: [CmmReg] -> RegisterFacts -> Maybe [CmmReg]
rwCmmRegs = rwCmmList rwCmmReg

-- rwCmmList takes a rewriting function and lifts it to a list. If at least
-- one element of a list was rewritten then the result is a list containing
-- both the rewritten elements and the not-rewritten ones. If none of the
-- elements in the list was rewritten the result is Nothing.
rwCmmList :: (a -> f -> Maybe a) -> [a] -> f -> Maybe [a]
rwCmmList f xs facts =
    case foldr rw (NoChange, []) xs of
      (NoChange  , _  ) -> Nothing
      (SomeChange, xs') -> Just xs'
    where
      rw x (flag, xs) =
          case f x facts of
            Nothing -> (flag      , x : xs)
            Just x' -> (SomeChange, x': xs)

-----------------------------------------------------------------------------
--                        Other utility function
-----------------------------------------------------------------------------

-}
-- Returns SomeChange if at least one element in the list is SomeChange.
-- Otherwise returns NoChange.
sumChanges :: [ChangeFlag] -> ChangeFlag
sumChanges []                = NoChange
sumChanges (SomeChange : _ ) = SomeChange
sumChanges (_          : xs) = sumChanges xs