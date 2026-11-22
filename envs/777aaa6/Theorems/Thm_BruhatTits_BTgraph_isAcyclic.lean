-- Prove2me | Theorems.Thm_BruhatTits_BTgraph_isAcyclic
-- name    : BruhatTits.BTgraph_isAcyclic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:24:04.030375+00:00
-- url     : https://prove2.me/theorems/63bf1aa0-5658-487e-8fad-8ee0756d3f02
-- title:
--   Bruhat Tits: BTgraph is Acyclic
-- statement:
--   The Bruhat-Tits graph has no loops, i.e. it is acyclic.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Tree.lean#L203-L213
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Tree.lean#L203-L213

import Definitions.Def_BruhatTits_Graph_GroupAction
import Definitions.Def_BruhatTits_Graph_Tree
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.BTgraph_isAcyclic : (BTgraph (R := R)).IsAcyclic := by sorry
