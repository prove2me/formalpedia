-- Prove2me | Theorems.Thm_BruhatTits_reachable
-- name    : BruhatTits.reachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:20:56.859297+00:00
-- url     : https://prove2.me/theorems/53e1e0ff-8d16-4046-82c1-af203cc630e0
-- title:
--   Bruhat Tits: reachable
-- statement:
--   There is a path between any two vertices.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Graph.lean#L41-L59
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Graph.lean#L41-L59

import Definitions.Def_BruhatTits_Graph_Edges
import Definitions.Def_BruhatTits_Graph_Graph
set_option autoImplicit false
suppress_compilation
open BruhatTits
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.reachable (M L : Vertices R) {n : ℕ} : (h : inv M L = n) → BTgraph.Reachable M L := by sorry
