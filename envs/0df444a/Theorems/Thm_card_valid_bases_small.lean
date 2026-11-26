-- Prove2me | Theorems.Thm_card_valid_bases_small
-- name    : card_valid_bases_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:44:42.015145+00:00
-- url     : https://prove2.me/theorems/2017007f-cdba-446e-acbe-e0bce4751634
-- title:
--   card valid bases small: card valid bases small
-- statement:
--   Exact table: `#(0) = 2`, `#(1) = 2`, `#(2) = 10`, `#(3) = 142`.
--
--   Source: https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/SmallN.lean#L413-L419
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/SmallN.lean#L413-L419

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

theorem card_valid_bases_small :
    Fintype.card (ValidBasis (Fin 0)) = 2 ∧
    Fintype.card (ValidBasis (Fin 1)) = 2 ∧
    Fintype.card (ValidBasis (Fin 2)) = 10 ∧
    Fintype.card (ValidBasis (Fin 3)) = 142 := by sorry
