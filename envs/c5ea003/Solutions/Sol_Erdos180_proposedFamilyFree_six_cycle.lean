-- Prove2me | solution 1 for Erdos180.proposedFamilyFree_six_cycle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:30:16.208395+00:00
-- url     : https://prove2.me/submissions/38468364-7ec6-464b-8cf8-62ce659437e1

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Theorems.Thm_Erdos180_proposedFamily_mem_iff

namespace Erdos180

noncomputable section
open Finset SimpleGraph

theorem six_cycle_mem_proposedFamily : finiteCycle 6 ∈ proposedFamily :=
  proposedFamily_mem_iff.mpr (.inl (.inl (.inr rfl)))

end

end Erdos180

open Erdos180
open Finset SimpleGraph

theorem solution
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree proposedFamily host) :
    (SimpleGraph.cycleGraph 6).Free host := by
  simpa [finiteCycle] using
    FamilyFree.member six_cycle_mem_proposedFamily hfree
