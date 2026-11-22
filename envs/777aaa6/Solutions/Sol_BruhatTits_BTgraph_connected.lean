-- Prove2me | solution 1 for BruhatTits.BTgraph_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:23:04.420179+00:00
-- url     : https://prove2.me/submissions/44883a1f-f9cd-4d17-b679-03d1529bd4e8

import Definitions.Def_BruhatTits_Graph_Edges
import Definitions.Def_BruhatTits_Graph_Graph
import Theorems.Thm_BruhatTits_reachable

set_option autoImplicit false
suppress_compilation
open BruhatTits
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]
namespace BruhatTits
theorem _root_.solution : SimpleGraph.Connected (BTgraph (R := R)) where
  preconnected M L := reachable M L rfl
end BruhatTits
