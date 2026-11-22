-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ModuleRealization.smul_as_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:12:30.907986+00:00
-- url     : https://prove2.me/submissions/d03490ae-5898-4d94-af2e-0add6678b43d

import Definitions.Def_Kourovka_Modules_SignedTameness
import Definitions.Def_Kourovka_Modules_ModuleRealization
import Theorems.Thm_Kourovka_MetabelianEnumeration_ModuleRealization_single_smul

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ModuleRealization
open FiniteCover ValuationModule SignedTameness TamenessCompactness
variable {k : ℕ} {M G : Type*} [AddCommGroup M] [Group G]
  [Module (GroupRing (Lattice k)) M]
namespace Kourovka.MetabelianEnumeration.ModuleRealization
theorem _root_.solution (p : GroupRing (Lattice k)) (m : M) :
    p • m = (p.support.toList.map fun u => p u •
      ((AddMonoidAlgebra.single u 1 : GroupRing (Lattice k)) • m)).sum := by
  rw [Finset.sum_map_toList]
  conv_lhs => rw [← AddMonoidAlgebra.sum_single p]
  change (∑ u ∈ p.support, AddMonoidAlgebra.single u (p u)) • m = _
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro u _
  exact single_smul u (p u) m
end Kourovka.MetabelianEnumeration.ModuleRealization
