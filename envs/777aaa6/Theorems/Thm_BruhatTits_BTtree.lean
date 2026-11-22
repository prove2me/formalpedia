-- Prove2me | Theorems.Thm_BruhatTits_BTtree
-- name    : BruhatTits.BTtree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:24:34.791014+00:00
-- url     : https://prove2.me/theorems/85f5f430-d6b7-47a7-991e-dd36440fc17e
-- title:
--   Bruhat Tits: BTtree
-- statement:
--   The Bruhat-Tits graph is a tree.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Tree.lean#L218-L220
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Tree.lean#L218-L220

import Definitions.Def_BruhatTits_Graph_GroupAction
import Definitions.Def_BruhatTits_Graph_Tree
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.BTtree : SimpleGraph.IsTree (BTgraph (R := R)) := by sorry
