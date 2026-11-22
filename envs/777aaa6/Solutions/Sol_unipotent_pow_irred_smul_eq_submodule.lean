-- Prove2me | solution 1 for unipotent_pow_irred_smul_eq_submodule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:51:46.243754+00:00
-- url     : https://prove2.me/submissions/bfaaf750-6cb6-4e14-b830-529199d1779b

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Definitions.Def_BruhatTits_Lattice_Transvect
import Theorems.Thm_P2M_Basis_transvect_apply__c6d95b5429da
import Theorems.Thm_P2M_Basis_transvect_apply__3554c878d91a
import Theorems.Thm_P2M_Basis_transvect__apply__1bdd29fda3f2
import Theorems.Thm_P2M_Basis_transvect__apply__03ca5877df1c
import Theorems.Thm_P2M_Basis_transvectEquiv_apply__b7ef14f0fd7c
import Theorems.Thm_P2M_Basis_transvectEquiv_apply__a337ed21e963
import Theorems.Thm_Basis_restrictToLattice_apply
import Theorems.Thm_Basis_restrict_apply
import Theorems.Thm_Basis_smulGL_apply
import Theorems.Thm_Basis_toLinear_symm_ofLinearEquiv_mulVec
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_LinearMap_GeneralLinearGroup_coe_ofLinearEquiv_bruhat2024
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_upperTriangularSubgroup_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_toLin_symm_apply
import Theorems.Thm_P2M_Basis_smul__apply_df6e729461ee
import Theorems.Thm_P2M_Basis_swap__apply__280e1e1cec15
import Theorems.Thm_P2M_Basis_swap__apply__cd04b6b0ed1e
import Theorems.Thm_P2M_Basis_swap__symm_e7ab2aa72738
import Theorems.Thm_P2M_Basis_swap_apply__293cd211b0be
import Theorems.Thm_P2M_Basis_swap_apply__dc9b61a54bcb
import Theorems.Thm_P2M_LinearMap_toMatrix__mulVec_bruhat2024_4481c521c4b9
import Theorems.Thm_Submodule_comap_subtype_smul
import Theorems.Thm_Submodule_map_subtype_smul
import Theorems.Thm_Subring_coe_det
import Theorems.Thm_Subring_coe_map_inv_mul_map
import Theorems.Thm_Subring_coe_map_mul_map_inv
import Theorems.Thm_Subtype_val_comp_add
import Theorems.Thm_Subtype_val_comp_single
import Theorems.Thm_Subtype_val_comp_smul
import Theorems.Thm_map_subtype_smul_standard_eq_standard
import Theorems.Thm_zaddVal_mul
import Theorems.Thm_zaddVal_units_map
attribute [local simp] Basis.restrictToLattice_apply
attribute [local simp] Basis.restrict_apply
attribute [local simp] Basis.smulGL_apply
attribute [local simp] Basis.toLinear_symm_ofLinearEquiv_mulVec
attribute [local simp] GL.coe_map_inv_mul_map
attribute [local simp] GL.coe_map_mul_map_inv
attribute [local simp] GL.map_apply
attribute [local simp] GL.map_inv_mul_map
attribute [local simp] GL.map_mul_map_inv
attribute [local simp] GL.map_one
attribute [local simp] LinearMap.GeneralLinearGroup.coe_ofLinearEquiv_bruhat2024
attribute [local simp] Matrix.BlockTriangular.fin_two_iff
attribute [local simp] Matrix.GeneralLinearGroup.mem_upperTriangularSubgroup_iff
attribute [local simp] Matrix.GeneralLinearGroup.toLin_symm_apply
attribute [local simp] P2M_Basis_smul__apply_df6e729461ee
attribute [local simp] P2M_Basis_swap__apply__280e1e1cec15
attribute [local simp] P2M_Basis_swap__apply__cd04b6b0ed1e
attribute [local simp] P2M_Basis_swap__symm_e7ab2aa72738
attribute [local simp] P2M_Basis_swap_apply__293cd211b0be
attribute [local simp] P2M_Basis_swap_apply__dc9b61a54bcb
attribute [local simp] P2M_LinearMap_toMatrix__mulVec_bruhat2024_4481c521c4b9
attribute [local simp] Submodule.comap_subtype_smul
attribute [local simp] Submodule.map_subtype_smul
attribute [local simp] Subring.coe_det
attribute [local simp] Subring.coe_map_inv_mul_map
attribute [local simp] Subring.coe_map_mul_map_inv
attribute [local simp] Subtype.val_comp_add
attribute [local simp] Subtype.val_comp_single
attribute [local simp] Subtype.val_comp_smul
attribute [local simp] map_subtype_smul_standard_eq_standard
attribute [local simp] zaddVal_mul
attribute [local simp] zaddVal_units_map


attribute [local simp] Basis.transvect_apply₀
attribute [local simp] Basis.transvect_apply₁
attribute [local simp] Basis.transvect'_apply₀
attribute [local simp] Basis.transvect'_apply₁
attribute [local simp] Basis.transvectEquiv_apply₀
attribute [local simp] Basis.transvectEquiv_apply₁

set_option autoImplicit false
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K}
theorem _root_.solution {ϖ : R} (hϖ : Irreducible ϖ)
    (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) (k n : ℕ) (hkn : k ≤ n) :
    b.unipotent (ϖ ^ n * x) • (b.ntwist₂ hϖ k 0).toSubmodule (R := R) =
      (b.ntwist₂ hϖ k 0).toSubmodule := by
  show Submodule.map ((Matrix.GeneralLinearGroup.toLin (b.unipotent _)).val : (Fin 2 → K) →ₗ[R] (Fin 2 → K)) _ = _
  have heq : (ϖ ^ n * x) • b 0 = (ϖ ^ (n - k) * x) • ϖ ^ k • b 0 := by
    conv_lhs => rw [show n = n - k + k by omega]
    rw [pow_add, mul_assoc]
    nth_rw 2 [mul_comm]
    rw [← mul_assoc, ← smul_smul]
  simp only [Basis.toSubmodule, Basis.unipotent, MulEquiv.apply_symm_apply,
    LinearMap.GeneralLinearGroup.coe_ofLinearEquiv_bruhat2024]
  rw [Submodule.map_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro - ⟨-, ⟨j, rfl⟩, rfl⟩
    simp only [Basis.transvectEquiv, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
      SetLike.mem_coe]
    match j with
    | 0 =>
    simp only [Fin.isValue, Basis.ntwist₂_apply₀]
    apply Submodule.subset_span
    use 0
    simp only [Fin.isValue, Basis.ntwist₂_apply₀, Subring.smul_def, SubmonoidClass.coe_pow,
      map_smul, Basis.equiv_apply, Equiv.refl_apply, Basis.transvect'_apply₀]
    | 1 =>
    simp only [Fin.isValue, Basis.ntwist₂_apply₁, pow_zero, one_smul, Basis.equiv_apply,
      Equiv.refl_apply, Basis.transvect'_apply₁]
    apply Submodule.add_mem
    · rw [heq]
      apply Submodule.smul_mem
      apply Submodule.subset_span
      use 0
      simp
    · apply Submodule.subset_span
      use 1
      simp
  · rw [Submodule.span_le]
    rintro - ⟨i, rfl⟩
    simp only [Basis.transvectEquiv, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
      SetLike.mem_coe]
    match i with
    | 0 =>
    simp only [Fin.isValue, Basis.ntwist₂_apply₀]
    apply Submodule.subset_span
    refine ⟨ϖ ^ k • b 0, ?_, ?_⟩
    · use 0
      simp
    · simp [Subring.smul_def, map_smul]
    | 1 =>
    simp only [Fin.isValue, Basis.ntwist₂_apply₁, pow_zero, one_smul]
    have : b 1 = (ϖ ^ n * x) • b 0 + b 1 - (ϖ ^ n * x) • b 0 := by simp
    rw [this]
    apply Submodule.sub_mem
    · apply Submodule.subset_span
      refine ⟨b 1, ?_, ?_⟩
      · use 1
        simp
      · simp
    · rw [heq]
      apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨ϖ ^ k • b 0, ?_, ?_⟩
      · use 0
        simp
      · simp [Subring.smul_def, map_smul]
