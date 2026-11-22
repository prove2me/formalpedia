-- Prove2me | Theorems.Thm_BruhatTits_BTgraph_connected
-- name    : BruhatTits.BTgraph_connected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:20:59.282083+00:00
-- url     : https://prove2.me/theorems/f8da4817-a86d-4dba-bd25-17dfea4514d2
-- title:
--   Bruhat Tits: BTgraph connected
-- statement:
--   The Bruhat-Tits graph is connected.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Graph.lean#L62-L63
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Graph.lean#L62-L63

import Definitions.Def_BruhatTits_Graph_Edges
import Definitions.Def_BruhatTits_Graph_Graph
set_option autoImplicit false
suppress_compilation
open BruhatTits
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.BTgraph_connected : SimpleGraph.Connected (BTgraph (R := R)) := by sorry
