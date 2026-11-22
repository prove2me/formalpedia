-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ValuationModule.lowerBound_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:57:31.247636+00:00
-- url     : https://prove2.me/submissions/b42a6cb6-59b4-4557-9b93-425ba76d4aad

import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.RingTheory.Finiteness.Nakayama
import Definitions.Def_Kourovka_Modules_ValuationModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_exists_common_lower_bound


set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ValuationModule
variable {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
variable {M : Type*} [AddCommGroup M] [Module (GroupRing Q) M]
omit [DecidableEq Q]
namespace Kourovka.MetabelianEnumeration.ValuationModule
theorem _root_.solution (χ : Q →+ ℝ) (p : GroupRing Q) : ∃ c, LowerBound χ p c := by
  obtain ⟨c, hc⟩ := FourierMotzkin.exists_common_lower_bound (p.support.toList.map χ)
  exact ⟨c, fun u hu => hc _ (List.mem_map.mpr ⟨u, Finset.mem_toList.mpr hu, rfl⟩)⟩
end Kourovka.MetabelianEnumeration.ValuationModule
