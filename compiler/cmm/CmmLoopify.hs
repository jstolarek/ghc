{-# LANGUAGE GADTs #-}
module CmmLoopify (
     cmmLoopify
  ) where

import Cmm
import CLabel
import CmmUtils
import Hoopl

-- This module implements loopification optimisation as described in
-- "Low-level code optimisations in the Glasgow Haskell Compiler" by
-- Krzysztod Wos. The idea is to take a CmmDecl - which is either data
-- section declaration or a procedure, but loopification only works
-- on procedures - and extract label of its info table. We also extract
-- label of the entry block (first block in a graph). Then we examine all
-- blocks in a procedure graph and whenever we encounter a tail-call
-- to procedure's info table we replace it with an uncoditional jump (goto).

cmmLoopify :: CmmDecl -> CmmGraph -> CmmGraph
cmmLoopify proc graph
   | Just nfo <- topInfoTable proc, nfo_lbl <- cit_lbl nfo
              = ofBlockList (g_entry graph) $ map (loopify nfo_lbl) blocks
   | otherwise = graph
  where
    blocks = toBlockListEntryFirst graph
    e_lbl  = entryLabel (head blocks)

    loopify :: CLabel -> CmmBlock -> CmmBlock
    loopify nfo_lbl = mapBlock rw_node
      where
        rw_node :: CmmNode e x -> CmmNode e x
        rw_node (CmmCall (CmmLit (CmmLabel lbl)) Nothing _ _ _ _)
          | lbl == nfo_lbl = CmmBranch e_lbl
        rw_node n = n
