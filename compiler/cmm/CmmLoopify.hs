{-# LANGUAGE GADTs #-}
module CmmLoopify (
     cmmLoopify
  ) where

import Cmm
import CLabel
import CmmUtils
import Hoopl

-- This module implements loopification and copying of the first basic
-- block of a loop as described in "Low-level code optimisations in the
-- Glasgow Haskell Compiler" by Krzysztof Wos. The idea is to take a CmmDecl
-- - which is either data section declaration or a procedure, but loopification
-- only works on procedures - and extract label of its info table. We also
-- extract label of the entry block (first block in a graph). Then we examine
-- all blocks in a procedure graph and whenever we encounter a tail-call
-- to procedure's info table we replace that call with a copy of the entry
-- block in the procedure. There are two consequences of this:
--    1. The block no longer does a tail-call. We instead have a goto, which
--       makes the loop more explicit
--    2. entry block of a procedure often loads parameters passed through the
--       stack into registers. By copying that code to the end of loop we
--       might have an opportunity for further optimisations, e.g. we may be
--       able to avoid using the stack by keeping all variables in registers
--
-- This pass converts this:
--
-- f.info_table {
--   L1: x = R1;
--       goto L2;
--   L2: if (x != 0) goto L3; else goto L4;
--   L3: ...
--      R1 = x;
--      tail_call.f()
--   L4: ...
-- }
--
-- to this:
--
-- f.info_table {
--   L1: x = R1;
--       goto L2;
--   L2: if (x != 0) goto L3; else goto L4;
--   L3: ...
--      R1 = x;
--      x = R1;
--      goto L2;
--   L4: ...
-- }
--
-- Obviously, the pair of assignments R1 = x; x = R1; is a no-op and can be
-- optimized away in later passes.

cmmLoopify :: CmmDecl -> CmmGraph -> CmmGraph
cmmLoopify proc graph
   | Just nfo <- topInfoTable proc, nfo_lbl <- cit_lbl nfo
              = ofBlockList (g_entry graph) $ map (loopify nfo_lbl) blocks
   | otherwise = graph
  where
    blocks         = toBlockListEntryFirst graph
    (_, entry_blk) = blockSplitHead $ head blocks

    loopify :: CLabel -> CmmBlock -> CmmBlock
    loopify nfo_lbl block = rw_node exit_node
        where
          (blk_head, exit_node) = blockSplitTail block
          rw_node :: CmmNode O C -> CmmBlock
          rw_node (CmmCall (CmmLit (CmmLabel lbl)) Nothing _ _ _ _)
            | lbl == nfo_lbl = blockAppend blk_head entry_blk
          rw_node _ = block

{- Note [Pre-CPS Loopification]

Loopification pass is done before converting Cmm to CPS form. This is signified
by Nothing in the rw_node pattern matching. That Nothing means that the node
being rewritten has no continuation, or in other words that the node represents
a tail call.

-}
