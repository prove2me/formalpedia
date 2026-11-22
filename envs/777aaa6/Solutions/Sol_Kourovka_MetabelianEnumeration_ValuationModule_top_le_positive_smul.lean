-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ValuationModule.top_le_positive_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:11:34.173644+00:00
-- url     : https://prove2.me/submissions/add20293-fe85-42ca-b12e-f06783da479b

import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.RingTheory.Finiteness.Nakayama
import Definitions.Def_Kourovka_Modules_ValuationModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_ValuationModule_exists_positive
import Theorems.Thm_Kourovka_MetabelianEnumeration_ValuationModule_positiveMonomial_mem

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ValuationModule
variable {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
variable {M : Type*} [AddCommGroup M] [Module (GroupRing Q) M]
namespace Kourovka.MetabelianEnumeration.ValuationModule
theorem _root_.solution (χ : Q →+ ℝ) (hχ : χ ≠ 0) :
    (⊤ : Submodule (nonnegativeRing χ) M) ≤ positiveIdeal χ • ⊤ := by
  obtain ⟨q, hq⟩ := exists_positive χ hχ
  intro m _
  have heq : positiveMonomial χ q hq • ((AddMonoidAlgebra.single (-q) 1 : GroupRing Q) • m) = m := by
    change (AddMonoidAlgebra.single q 1 : GroupRing Q) •
      ((AddMonoidAlgebra.single (-q) 1 : GroupRing Q) • m) = m
    rw [← mul_smul, AddMonoidAlgebra.single_mul_single]
    simp [← AddMonoidAlgebra.one_def]
  rw [← heq]
  exact Submodule.smul_mem_smul (positiveMonomial_mem χ q hq) (Submodule.mem_top)
end Kourovka.MetabelianEnumeration.ValuationModule
