-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ValuationModule.scalar_replacement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:12:03.119121+00:00
-- url     : https://prove2.me/submissions/711c9114-d893-4282-81ac-328ffa612710

import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.RingTheory.Finiteness.Nakayama
import Definitions.Def_Kourovka_Modules_ValuationModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_ValuationModule_lowerBound_mul
import Theorems.Thm_Kourovka_MetabelianEnumeration_ValuationModule_lowerBound_pow
import Theorems.Thm_Kourovka_MetabelianEnumeration_ValuationModule_lowerBound_exists
import Theorems.Thm_Kourovka_MetabelianEnumeration_ValuationModule_positive_lowerBound_exists
import Theorems.Thm_Kourovka_MetabelianEnumeration_ValuationModule_centralizer_pow

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ValuationModule
variable {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
variable {M : Type*} [AddCommGroup M] [Module (GroupRing Q) M]
namespace Kourovka.MetabelianEnumeration.ValuationModule
theorem _root_.solution (χ : Q →+ ℝ) (p : GroupRing Q)
    (hp : ∀ u ∈ p.support, 0 < χ u) (hact : ∀ m : M, p • m = m)
    (r : GroupRing Q) : ∃ s : nonnegativeRing χ, ∀ m : M, s • m = r • m := by
  obtain ⟨c, hc⟩ := lowerBound_exists χ r
  obtain ⟨d, hd, hdp⟩ := positive_lowerBound_exists χ p hp
  obtain ⟨n, hn⟩ := exists_nat_gt (-c / d)
  have hcn : 0 ≤ c + n * d := by
    have := (div_lt_iff₀ hd).mp hn
    linarith
  have hprod := lowerBound_mul χ hc (lowerBound_pow χ hdp n)
  refine ⟨⟨r * p ^ n, fun u hu => hcn.trans (hprod u hu)⟩, ?_⟩
  intro m
  change (r * p ^ n) • m = r • m
  rw [mul_smul, centralizer_pow hact]
end Kourovka.MetabelianEnumeration.ValuationModule
