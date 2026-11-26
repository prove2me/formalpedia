-- Prove2me | Theorems.Thm_numBases_eq_filter
-- name    : numBases_eq_filter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:44:33.791821+00:00
-- url     : https://prove2.me/theorems/e54b47d1-92c9-4969-8721-67c8fb357ce4
-- title:
--   num Bases eq filter: num Bases eq filter
-- statement:
--   The num Bases eq filter construction uses the num Bases eq filter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/SmallN.lean#L376-L382
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/SmallN.lean#L376-L382

import Definitions.Def_CARDB
import Mathlib.Combinatorics.Colex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_CARDB_SmallN
set_option autoImplicit true
open Set TopologicalSpace
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
variable {n : ℕ}

theorem numBases_eq_filter (n : ℕ) :
    numBases n =
      ((Finset.range (2 ^ (2 ^ n))).filter fun m => isBasisNat n m = true).card := by sorry
