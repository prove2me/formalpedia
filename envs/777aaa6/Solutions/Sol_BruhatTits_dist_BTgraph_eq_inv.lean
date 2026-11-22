-- Prove2me | solution 1 for BruhatTits.dist_BTgraph_eq_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T19:02:18.86049+00:00
-- url     : https://prove2.me/submissions/ab2299c5-d835-40ba-989d-898bb17be6cb

import Definitions.Def_BruhatTits_Graph_GroupAction
import Definitions.Def_BruhatTits_Graph_Tree
import Theorems.Thm_BruhatTits_length_eq_inv
import Theorems.Thm_BruhatTits_BTgraph_connected


set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]
namespace BruhatTits
theorem _root_.solution : (BTgraph (R := R)).dist = inv := by
  ext x y
  obtain ⟨p, hp, hlen⟩ := (BTgraph_connected (R := R)).exists_path_of_dist x y
  rw [← hlen, length_eq_inv hp.isTrail]
end BruhatTits
