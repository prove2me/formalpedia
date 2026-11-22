-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ValuationModule.positive_centralizer_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:12:30.446186+00:00
-- url     : https://prove2.me/submissions/aae9c41c-8a31-4f7b-9d89-976273175447

import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.RingTheory.Finiteness.Nakayama
import Definitions.Def_Kourovka_Modules_ValuationModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_ValuationModule_top_le_positive_smul

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ValuationModule
variable {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
variable {M : Type*} [AddCommGroup M] [Module (GroupRing Q) M]
namespace Kourovka.MetabelianEnumeration.ValuationModule
theorem _root_.solution (χ : Q →+ ℝ) (hχ : χ ≠ 0)
    [Module.Finite (nonnegativeRing χ) M] :
    ∃ p : GroupRing Q, (∀ u ∈ p.support, 0 < χ u) ∧ ∀ m : M, p • m = m := by
  obtain ⟨p, hp, hact⟩ := Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul
    (positiveIdeal χ) (⊤ : Submodule (nonnegativeRing χ) M) Module.Finite.fg_top
      (top_le_positive_smul (M := M) χ hχ)
  exact ⟨p, hp, fun m => hact m (Submodule.mem_top)⟩
end Kourovka.MetabelianEnumeration.ValuationModule
