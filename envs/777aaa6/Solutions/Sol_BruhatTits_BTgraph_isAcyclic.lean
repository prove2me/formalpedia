-- Prove2me | solution 1 for BruhatTits.BTgraph_isAcyclic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T19:02:18.334003+00:00
-- url     : https://prove2.me/submissions/41380e80-84e8-4daf-bc74-645c5b568235

import Definitions.Def_BruhatTits_Graph_GroupAction
import Definitions.Def_BruhatTits_Graph_Tree
import Theorems.Thm_BruhatTits_length_eq_inv
import Theorems.Thm_BruhatTits_inv_self


set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]
namespace BruhatTits
theorem _root_.solution : (BTgraph (R := R)).IsAcyclic := by
  -- suppose `c` is a circle
  intro x c h
  -- then `c` is a trail, but the length of such a chain is the distance
  -- of the endpoints, which yields a contradiction
  have : c.length = inv x x := length_eq_inv h.isCircuit.isTrail
  rw [inv_self] at this
  have : 3 ≤ 0 := by
    rw [← this]
    exact SimpleGraph.Walk.IsCycle.three_le_length h
  contradiction
end BruhatTits
