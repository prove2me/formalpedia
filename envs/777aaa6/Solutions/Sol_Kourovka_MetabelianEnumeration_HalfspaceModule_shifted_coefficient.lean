-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceModule.shifted_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:15:03.068724+00:00
-- url     : https://prove2.me/submissions/47567a6e-95d6-49f1-bf83-0b6af068aa1a

import Definitions.Def_Kourovka_Modules_ValuationModule
import Definitions.Def_Kourovka_Halfspaces_HalfspaceModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceModule_monomial_lower_bound
import Theorems.Thm_Kourovka_MetabelianEnumeration_ValuationModule_lowerBound_exists
import Theorems.Thm_Kourovka_MetabelianEnumeration_ValuationModule_lowerBound_mul


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceModule
open ValuationModule
variable {Q M : Type} [AddCommGroup Q] [DecidableEq Q]
variable [AddCommGroup M] [Module (GroupRing Q) M]
namespace Kourovka.MetabelianEnumeration.HalfspaceModule
theorem _root_.solution (χ : Q →+ ℝ) (u : Q) (hu : 0 < χ u)
    (r : GroupRing Q) : ∃ n : ℕ, monomial (n • u) * r ∈ nonnegativeRing χ := by
  obtain ⟨c, hc⟩ := lowerBound_exists χ r
  obtain ⟨n, hn⟩ := exists_nat_gt (-c / χ u)
  have hpos : 0 ≤ (n : ℝ) * χ u + c := by
    have := (div_lt_iff₀ hu).mp hn
    linarith
  refine ⟨n, ?_⟩
  intro q hq
  have h := lowerBound_mul χ (monomial_lower_bound χ (n • u)) hc q hq
  simp only [map_nsmul, nsmul_eq_mul] at h
  exact hpos.trans h
end Kourovka.MetabelianEnumeration.HalfspaceModule
