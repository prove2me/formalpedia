-- Prove2me | solution 1 for Basis.twist_le_twist_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:13:32.91796+00:00
-- url     : https://prove2.me/submissions/62ac1ac2-3886-43c8-90d9-95c48738cd21

import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Definitions.Def_BruhatTits_Lattice_Construction
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_upperTriangularSubgroup_iff
import Theorems.Thm_Subring_coe_det
import Theorems.Thm_Subring_coe_map_inv_mul_map
import Theorems.Thm_Subring_coe_map_mul_map_inv
import Theorems.Thm_Subtype_val_comp_add
import Theorems.Thm_Subtype_val_comp_single
import Theorems.Thm_Subtype_val_comp_smul
import Theorems.Thm_irreducible_zpow_mem_subring_iff
import Theorems.Thm_zaddVal_mul
import Theorems.Thm_zaddVal_units_map
attribute [local simp] GL.coe_map_inv_mul_map
attribute [local simp] GL.coe_map_mul_map_inv
attribute [local simp] GL.map_apply
attribute [local simp] GL.map_inv_mul_map
attribute [local simp] GL.map_mul_map_inv
attribute [local simp] GL.map_one
attribute [local simp] Matrix.BlockTriangular.fin_two_iff
attribute [local simp] Matrix.GeneralLinearGroup.mem_upperTriangularSubgroup_iff
attribute [local simp] Subring.coe_det
attribute [local simp] Subring.coe_map_inv_mul_map
attribute [local simp] Subring.coe_map_mul_map_inv
attribute [local simp] Subtype.val_comp_add
attribute [local simp] Subtype.val_comp_single
attribute [local simp] Subtype.val_comp_smul
attribute [local simp] zaddVal_mul
attribute [local simp] zaddVal_units_map



set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits
open Basis
variable {ι : Type*}
open BigOperators
namespace Basis
theorem _root_.solution [Fintype ι] (b : Basis ι K (ι → K)) {ϖ : R} (hϖ : Irreducible ϖ) (f g : ι → ℤ) :
    (b.twist hϖ f).toSubmodule (R := R) ≤ (b.twist hϖ g).toSubmodule (R := R) ↔ g ≤ f := by
  classical
  constructor
  · intro h i
    have : ϖ.val ^ f i • b i ∈ (b.twist hϖ g).toSubmodule (R := R) := by
      apply h
      apply Submodule.subset_span
      use i
      simp
    simp only [toSubmodule] at this
    rw [Submodule.mem_span_range_iff_exists_fun] at this
    obtain ⟨c, hc⟩ := this
    have heq : ∑ j : ι, c j • (b.twist hϖ g) j - ϖ.val ^ f i • b i = 0 := by
      rw [hc]
      simp
    simp at heq
    have : ϖ.val ^ f i • b i = ∑ j : ι, (if i = j then ϖ.val ^ f i else 0) • b j := by
      simp
    rw [this] at heq
    rw [← Finset.sum_sub_distrib] at heq
    simp_rw [Subring.smul_def, smul_smul, ← sub_smul] at heq
    have hzero := Fintype.linearIndependent_iff.mp b.linearIndependent _ heq i
    simp at hzero
    rw [sub_eq_zero] at hzero
    have : ϖ.val ≠ 0 := by simpa using hϖ.ne_zero
    have : ϖ.val ^ g i ≠ 0 := zpow_ne_zero (g i) this
    have : (c i).val = ϖ.val ^ f i * ϖ.val ^ (- g i) := by
      rw [← hzero]
      simp
      field_simp
    rw [← zpow_add₀] at this
    have : f i - g i ≥ 0 := by
      rw [← irreducible_zpow_mem_subring_iff (R := R) (hϖ := hϖ)]
      rw [show f i - g i = f i + -g i by rfl, ← this]
      exact (c i).property
    simpa using this
    simpa using hϖ.ne_zero
  · intro hgf
    simp only [toSubmodule]
    rw [Submodule.span_le]
    rintro - ⟨i, hi, rfl⟩
    simp only [twist_apply, SetLike.mem_coe]
    have hϖ' : ϖ.val ≠ 0 := by simpa using hϖ.ne_zero
    have : ϖ.val ^ g i ≠ 0 := zpow_ne_zero (g i) hϖ'
    have : ϖ.val ^ f i • b i = ϖ.val ^ (f i - g i) • ϖ.val ^ g i • b i := by
      rw [zpow_sub₀ hϖ', smul_smul]
      field_simp
    rw [this]
    have : ϖ.val ^ (f i - g i) ∈ R := by
      rw [irreducible_zpow_mem_subring_iff (hϖ := hϖ)]
      simpa using hgf i
    let r : R := ⟨ϖ.val ^ (f i - g i), this⟩
    have : ϖ.val ^ (f i - g i) • ϖ.val ^ g i • b i = r • ϖ.val ^ g i • b i := by
      simp [Subring.smul_def, r]
    rw [this]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    use i
    simp
end Basis
