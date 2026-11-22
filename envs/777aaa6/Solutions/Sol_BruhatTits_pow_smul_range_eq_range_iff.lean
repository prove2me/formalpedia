-- Prove2me | solution 1 for BruhatTits.pow_smul_range_eq_range_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:23:42.468275+00:00
-- url     : https://prove2.me/submissions/a7b3700a-2334-41a5-b02e-c2d73da46591

import Definitions.Def_BruhatTits_Graph_Graph
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Graph_GroupAction
import Theorems.Thm_Basis_restrictToLattice_apply
import Theorems.Thm_Basis_restrict_apply
import Theorems.Thm_Basis_smulGL_apply
import Theorems.Thm_Basis_toLinear_symm_ofLinearEquiv_mulVec
import Theorems.Thm_BruhatTits_dist_self
import Theorems.Thm_BruhatTits_dist_smul_GL_eq_dist
import Theorems.Thm_BruhatTits_inv_mk
import Theorems.Thm_BruhatTits_mulBasisScalar_apply
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_LinearMap_GeneralLinearGroup_coe_ofLinearEquiv_bruhat2024
import Theorems.Thm_List_smul_lattice_length
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_upperTriangularSubgroup_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_toLin_symm_apply
import Theorems.Thm_P2M_Basis_smul__apply_df6e729461ee
import Theorems.Thm_P2M_Basis_swap__apply__280e1e1cec15
import Theorems.Thm_P2M_Basis_swap__apply__cd04b6b0ed1e
import Theorems.Thm_P2M_Basis_swap__symm_e7ab2aa72738
import Theorems.Thm_P2M_Basis_swap_apply__293cd211b0be
import Theorems.Thm_P2M_Basis_swap_apply__dc9b61a54bcb
import Theorems.Thm_P2M_Basis_transvectEquiv_apply__a337ed21e963
import Theorems.Thm_P2M_Basis_transvectEquiv_apply__b7ef14f0fd7c
import Theorems.Thm_P2M_Basis_transvectResidue_apply__556496910c93
import Theorems.Thm_P2M_Basis_transvectResidue_apply__d9f90c0bfc03
import Theorems.Thm_P2M_Basis_transvect__apply__03ca5877df1c
import Theorems.Thm_P2M_Basis_transvect__apply__1bdd29fda3f2
import Theorems.Thm_P2M_Basis_transvect_apply__3554c878d91a
import Theorems.Thm_P2M_Basis_transvect_apply__c6d95b5429da
import Theorems.Thm_P2M_LinearMap_toMatrix__mulVec_bruhat2024_4481c521c4b9
import Theorems.Thm_Submodule_comap_subtype_smul
import Theorems.Thm_Submodule_map_subtype_smul
import Theorems.Thm_Subring_coe_det
import Theorems.Thm_Subring_coe_map_inv_mul_map
import Theorems.Thm_Subring_coe_map_mul_map_inv
import Theorems.Thm_Subtype_val_comp_add
import Theorems.Thm_Subtype_val_comp_single
import Theorems.Thm_Subtype_val_comp_smul
import Theorems.Thm_cartanDiag_zero
import Theorems.Thm_conj_cartanDiag_one_one
import Theorems.Thm_conj_cartanDiag_one_zero
import Theorems.Thm_conj_cartanDiag_zero_one
import Theorems.Thm_conj_cartanDiag_zero_zero
import Theorems.Thm_irreducible_zpow_mem_subring_iff
import Theorems.Thm_map_subtype_smul_standard_eq_standard
import Theorems.Thm_valuation_eq_one_iff
import Theorems.Thm_valuation_irreducible_zpow_eq_one_iff
import Theorems.Thm_zaddVal_mul
import Theorems.Thm_zaddVal_units_map
attribute [local simp] Basis.restrictToLattice_apply
attribute [local simp] Basis.restrict_apply
attribute [local simp] Basis.smulGL_apply
attribute [local simp] Basis.toLinear_symm_ofLinearEquiv_mulVec
attribute [local simp] BruhatTits.dist_self
attribute [local simp] BruhatTits.dist_smul_GL_eq_dist
attribute [local simp] BruhatTits.inv_mk
attribute [local simp] BruhatTits.mulBasisScalar_apply
attribute [local simp] GL.coe_map_inv_mul_map
attribute [local simp] GL.coe_map_mul_map_inv
attribute [local simp] GL.map_apply
attribute [local simp] GL.map_inv_mul_map
attribute [local simp] GL.map_mul_map_inv
attribute [local simp] GL.map_one
attribute [local simp] LinearMap.GeneralLinearGroup.coe_ofLinearEquiv_bruhat2024
attribute [local simp] List.smul_lattice_length
attribute [local simp] Matrix.BlockTriangular.fin_two_iff
attribute [local simp] Matrix.GeneralLinearGroup.mem_upperTriangularSubgroup_iff
attribute [local simp] Matrix.GeneralLinearGroup.toLin_symm_apply
attribute [local simp] P2M_Basis_smul__apply_df6e729461ee
attribute [local simp] P2M_Basis_swap__apply__280e1e1cec15
attribute [local simp] P2M_Basis_swap__apply__cd04b6b0ed1e
attribute [local simp] P2M_Basis_swap__symm_e7ab2aa72738
attribute [local simp] P2M_Basis_swap_apply__293cd211b0be
attribute [local simp] P2M_Basis_swap_apply__dc9b61a54bcb
attribute [local simp] P2M_Basis_transvectEquiv_apply__a337ed21e963
attribute [local simp] P2M_Basis_transvectEquiv_apply__b7ef14f0fd7c
attribute [local simp] P2M_Basis_transvectResidue_apply__556496910c93
attribute [local simp] P2M_Basis_transvectResidue_apply__d9f90c0bfc03
attribute [local simp] P2M_Basis_transvect__apply__03ca5877df1c
attribute [local simp] P2M_Basis_transvect__apply__1bdd29fda3f2
attribute [local simp] P2M_Basis_transvect_apply__3554c878d91a
attribute [local simp] P2M_Basis_transvect_apply__c6d95b5429da
attribute [local simp] P2M_LinearMap_toMatrix__mulVec_bruhat2024_4481c521c4b9
attribute [local simp] Submodule.comap_subtype_smul
attribute [local simp] Submodule.map_subtype_smul
attribute [local simp] Subring.coe_det
attribute [local simp] Subring.coe_map_inv_mul_map
attribute [local simp] Subring.coe_map_mul_map_inv
attribute [local simp] Subtype.val_comp_add
attribute [local simp] Subtype.val_comp_single
attribute [local simp] Subtype.val_comp_smul
attribute [local simp] cartanDiag_zero
attribute [local simp] conj_cartanDiag_one_one
attribute [local simp] conj_cartanDiag_one_zero
attribute [local simp] conj_cartanDiag_zero_one
attribute [local simp] conj_cartanDiag_zero_zero
attribute [local simp] map_subtype_smul_standard_eq_standard
attribute [local simp] zaddVal_mul
attribute [local simp] zaddVal_units_map



set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
open BruhatTits
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
open Pointwise
namespace BruhatTits
theorem _root_.solution {ι : Type*} [Finite ι] [Nonempty ι] {ϖ : R}
    (hϖ : Irreducible ϖ) (n : ℤ) :
    ϖ.val ^ n • Set.range ((Algebra.linearMap R K).compLeft ι) =
      Set.range ((Algebra.linearMap R K).compLeft ι) ↔ n = 0 := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; simp⟩
  let i : ι := ‹Nonempty ι›.some
  by_cases hn : n ≥ 0
  · rw [Set.ext_iff] at h
    have : (Pi.basisFun K ι) i ∈ ϖ.val ^ n • Set.range ⇑((Algebra.linearMap (↥R) K).compLeft ι) := by
      rw [h]
      use Pi.basisFun R ι i
      ext
      simp [Algebra.algebraMap_ofSubring_apply, Pi.single_apply]
    simp at this
    rw [Set.mem_smul_set] at this
    obtain ⟨-, ⟨z, rfl⟩, hy⟩ := this
    rw [funext_iff] at hy
    have := hy i
    simp [Algebra.algebraMap_ofSubring_apply] at this
    have heq : (ValuationRing.valuation R K) (z i).val = 1 := by
      rw [← valuation_eq_one_iff, isUnit_iff_exists_inv']
      use ⟨ϖ.val ^ n, (irreducible_zpow_mem_subring_iff ϖ hϖ n).mpr hn⟩
      ext
      simpa
    apply_fun (ValuationRing.valuation R K ·) at this
    simp [-map_zpow₀] at this
    rw [heq] at this
    simp [-map_zpow₀] at this
    rwa [valuation_irreducible_zpow_eq_one_iff _ hϖ] at this
  · have : Pi.single i (ϖ.val ^ n) ∈ Set.range ((Algebra.linearMap (↥R) K).compLeft ι) := by
      rw [← h]
      rw [Set.mem_smul_set]
      refine ⟨Pi.single i 1, ?_, ?_⟩
      use Pi.single i 1
      ext
      simp [Algebra.algebraMap_ofSubring_apply, Pi.single_apply]
      ext j
      simp [Pi.single_apply]
    simp at this
    obtain ⟨z, hz⟩ := this
    rw [funext_iff] at hz
    have := hz i
    simp [Algebra.algebraMap_ofSubring_apply] at this
    have : ϖ.val ^ n ∈ R := by
      rw [← this]
      exact (z i).property
    rw [irreducible_zpow_mem_subring_iff _ hϖ] at this
    omega
end BruhatTits
