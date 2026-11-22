-- Prove2me | solution 1 for BruhatTits.BTtree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T19:04:36.897757+00:00
-- url     : https://prove2.me/submissions/15d51d01-0057-4145-bf88-d0e651174461

import Definitions.Def_BruhatTits_Graph_GroupAction
import Definitions.Def_BruhatTits_Graph_Tree
import Theorems.Thm_BruhatTits_BTgraph_isAcyclic
import Theorems.Thm_BruhatTits_BTgraph_connected


set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]
namespace BruhatTits
theorem _root_.solution : SimpleGraph.IsTree (BTgraph (R := R)) where
  isConnected := BTgraph_connected
  IsAcyclic := BTgraph_isAcyclic
end BruhatTits
