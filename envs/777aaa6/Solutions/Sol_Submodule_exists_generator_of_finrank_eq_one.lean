-- Prove2me | solution 1 for Submodule.exists_generator_of_finrank_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:55:27.963336+00:00
-- url     : https://prove2.me/submissions/41fd8ebe-596b-4caf-83c3-e8429eb1c24f

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Theorems.Thm_Subtype_val_comp_add
import Theorems.Thm_Subtype_val_comp_single
import Theorems.Thm_Subtype_val_comp_smul
attribute [local simp] Subtype.val_comp_add
attribute [local simp] Subtype.val_comp_single
attribute [local simp] Subtype.val_comp_smul



set_option autoImplicit false
variable {R M : Type*} [Field R]  [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]
namespace Submodule
theorem _root_.solution (p : Submodule R M) (h : Module.finrank R p = 1) :
    ∃ (v : M), v ≠ 0 ∧ Submodule.span R {v} = p := by
  have : p ≠ ⊥ := by rw [← p.one_le_finrank_iff, h]
  rw [p.ne_bot_iff] at this
  obtain ⟨v, hvmem, hv⟩ := this
  refine ⟨v, hv, ?_⟩
  have : (⟨v, hvmem⟩ : p) ≠ 0 := by simpa
  rw [finrank_eq_one_iff_of_nonzero (K := R) _ this] at h
  apply le_antisymm
  · rw [Submodule.span_le]
    simpa only [Set.singleton_subset_iff, SetLike.mem_coe, ne_eq, AddSubmonoid.mk_eq_zero]
  · intro x hx
    have hx' : (⟨x, hx⟩ : p) ∈ Submodule.span R {⟨v, hvmem⟩} := by
      rw [h]
      trivial
    rw [Submodule.mem_span_singleton] at hx' ⊢
    simp only [SetLike.mk_smul_mk, Subtype.mk.injEq] at hx'
    assumption
end Submodule
