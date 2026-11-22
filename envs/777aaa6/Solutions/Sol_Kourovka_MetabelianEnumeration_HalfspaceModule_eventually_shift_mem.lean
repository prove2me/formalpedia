-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceModule.eventually_shift_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:15:50.318584+00:00
-- url     : https://prove2.me/submissions/561ab994-5e59-442a-9e69-7980e171c1a3

import Definitions.Def_Kourovka_Modules_ValuationModule
import Definitions.Def_Kourovka_Halfspaces_HalfspaceModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceModule_monomial_add
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceModule_shift_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceModule_shift_nsmul_mem
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceModule_shifted_coefficient

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceModule
open ValuationModule
variable {Q M : Type} [AddCommGroup Q] [DecidableEq Q]
variable [AddCommGroup M] [Module (GroupRing Q) M]
namespace Kourovka.MetabelianEnumeration.HalfspaceModule
theorem _root_.solution (χ : Q →+ ℝ) (u : Q) (hu : 0 < χ u)
    (V : Submodule (nonnegativeRing χ) M) (m : M)
    (hm : m ∈ Submodule.span (GroupRing Q) (V : Set M)) :
    ∃ n : ℕ, shift (n • u) m ∈ V := by
  induction hm using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    refine ⟨i + j, ?_⟩
    rw [shift_add]
    apply V.add_mem
    · have h := shift_nsmul_mem χ V u hu.le j _ hi
      simpa only [shift_shift, add_nsmul, add_comm] using h
    · have h := shift_nsmul_mem χ V u hu.le i _ hj
      simpa only [shift_shift, add_nsmul] using h
  | smul r x _ hx =>
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := shifted_coefficient χ u hu r
    refine ⟨j + i, ?_⟩
    have h := V.smul_mem (⟨monomial (j • u) * r, hj⟩ : nonnegativeRing χ) hi
    have heq : shift ((j + i) • u) (r • x) =
        (⟨monomial (j • u) * r, hj⟩ : nonnegativeRing χ) • shift (i • u) x := by
      change monomial ((j + i) • u) • (r • x) =
        (monomial (j • u) * r) • (monomial (i • u) • x)
      rw [add_nsmul, monomial_add, mul_smul, mul_smul]
      rw [smul_comm (monomial (i • u)) r x]
    exact heq.symm ▸ h
end Kourovka.MetabelianEnumeration.HalfspaceModule
