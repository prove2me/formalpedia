-- Prove2me | solution 1 for Submodule.exists_generator_of_finrank_eq_one_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:58:07.191646+00:00
-- url     : https://prove2.me/submissions/65a963c3-9bc3-4b78-a7fe-42c31c2b710d

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Theorems.Thm_Submodule_exists_generator_of_finrank_eq_one
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
theorem _root_.solution (b : Basis (Fin 2) R M) (p : Submodule R M)
    (hr : Module.finrank R p = 1)
    (ht : p ≠ Submodule.span R {b 0}) :
    ∃ (a : R), p = Submodule.span R { a • b 0 + b 1 } := by
  obtain ⟨v, hv, hvspan⟩ := p.exists_generator_of_finrank_eq_one hr
  have : v ∈ Submodule.span R (Set.range b) := by rw [b.span_eq]; trivial
  let c : Fin 2 → R := b.repr v
  let β : R := c 1
  have hvr : v = c 0 • b 0 + β • b 1 := by
    rw [b.ext_elem_iff]
    intro i
    match i with
    | 0 => simp [c]
    | 1 => simp [c, β]
  have : β ≠ 0 := by
    intro hβ
    simp [hβ] at hvr
    have : c 0 ≠ 0 := by
      intro hc
      rw [hc] at hvr
      simp at hvr
      contradiction
    apply ht
    rw [← hvspan, hvr]
    apply le_antisymm
    · rw [Submodule.span_le]
      simp only [Fin.isValue, Set.singleton_subset_iff, SetLike.mem_coe]
      apply Submodule.smul_mem
      apply Submodule.subset_span
      simp
    · rw [Submodule.span_le]
      simp only [Fin.isValue, Set.singleton_subset_iff, SetLike.mem_coe]
      have : b 0 = (c 0)⁻¹ • c 0 • b 0 := by
        rw [smul_smul]
        field_simp
        simp only [one_smul]
      nth_rw 2 [this]
      apply Submodule.smul_mem
      apply Submodule.subset_span
      simp
  use c 0 / β
  rw [← hvspan, hvr]
  apply le_antisymm
  · rw [Submodule.span_le]
    have : c 0 • b 0 + β • b 1 = β • ((c 0 / β) • b 0 + b 1) := by
      simp [smul_add, smul_smul, div_eq_mul_inv, this, mul_comm, mul_left_comm]
    simp only [Fin.isValue, Set.singleton_subset_iff, SetLike.mem_coe]
    nth_rw 1 [this]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    simp
  · rw [Submodule.span_le]
    simp only [Fin.isValue, Set.singleton_subset_iff, SetLike.mem_coe]
    have : (c 0 / β) • b 0 + b 1 = (1 / β) • (c 0 • b 0 + β • b 1) := by
      simp [smul_smul]
      field_simp
      simp only [one_smul]
    nth_rw 1 [this]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    simp
end Submodule
