-- Prove2me | solution 1 for BruhatTits.reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:21:04.290183+00:00
-- url     : https://prove2.me/submissions/5914e423-46a7-42dc-b7b9-85a58ec9ac7f

import Definitions.Def_BruhatTits_Graph_Edges
import Definitions.Def_BruhatTits_Graph_Graph
import Theorems.Thm_BruhatTits_eq_iff
import Theorems.Thm_BruhatTits_exists_intermediate_vertex
import Theorems.Thm_BruhatTits_inv_symm


set_option autoImplicit false
suppress_compilation
open BruhatTits
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]
namespace BruhatTits
theorem _root_.solution (M L : Vertices R) {n : ℕ} : (h : inv M L = n) → BTgraph.Reachable M L := by
  revert M L
  induction n with
  | zero =>
    intro M L h
    rw [← eq_iff] at h
    subst h
    rfl
  | succ k ih =>
    intro M L h
    obtain ⟨T, hLT, hTM⟩ := exists_intermediate_vertex _ M L h
    apply SimpleGraph.Reachable.trans
    · apply SimpleGraph.Reachable.symm
      apply SimpleGraph.Adj.reachable
      exact hTM
    · show BTgraph.Reachable T L
      apply ih
      rw [inv_symm]
      exact hLT
end BruhatTits
