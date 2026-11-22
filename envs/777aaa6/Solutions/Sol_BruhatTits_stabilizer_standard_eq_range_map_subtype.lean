-- Prove2me | solution 1 for BruhatTits.stabilizer_standard_eq_range_map_subtype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:25:53.754214+00:00
-- url     : https://prove2.me/submissions/1b81c730-db09-413b-ba01-e69d42fe3090

import Definitions.Def_BruhatTits_Graph_Graph
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Graph_GroupAction
import Theorems.Thm_BruhatTits_cartanDiag_smul_standard
import Theorems.Thm_BruhatTits_pow_smul_range_eq_range_iff
import Theorems.Thm_Basis_restrictToLattice_apply
import Theorems.Thm_Basis_restrict_apply
import Theorems.Thm_Basis_smulGL_apply
import Theorems.Thm_Basis_toLinear_symm_ofLinearEquiv_mulVec
import Theorems.Thm_BruhatTits_dist_self
import Theorems.Thm_BruhatTits_dist_smul_GL_eq_dist
import Theorems.Thm_BruhatTits_dist_twist
import Theorems.Thm_BruhatTits_inv_mk
import Theorems.Thm_BruhatTits_mulBasisScalar_apply
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_eq
import Theorems.Thm_GL_map_inv
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_Lattice_standard_M
import Theorems.Thm_LinearMap_GeneralLinearGroup_coe_ofLinearEquiv_bruhat2024
import Theorems.Thm_List_smul_lattice_length
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_diagonal_smul
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
import Theorems.Thm_P2M_cartan_decomposition__b636da006c62
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
import Theorems.Thm_map_subtype_smul_standard_eq_standard
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
theorem _root_.solution :
    MulAction.stabilizer (GL (Fin 2) K) (Lattice.standard R) =
      (Matrix.GeneralLinearGroup.map R.subtype).range := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  ext g
  simp only [MulAction.mem_stabilizer_iff, MonoidHom.mem_range]
  constructor
  · intro hg
    obtain ⟨(k₁ : GL (Fin 2) R), (k₂ : GL (Fin 2) R), (f : Fin 2 → ℤ), hf, h⟩ :=
      cartan_decomposition' (k := 2) ϖ hϖ g
    rw [← h] at hg
    erw [mul_smul, GL_map_eq, GL_map_eq, map_subtype_smul_standard_eq_standard k₂, mul_smul] at hg
    apply_fun (Matrix.GeneralLinearGroup.map R.subtype k₁⁻¹ • ·) at hg
    simp only [map_inv, PNat.val_ofNat, inv_smul_smul] at hg
    simp only [← SemigroupAction.mul_smul, inv_mul_cancel_left] at hg
    rw [← map_inv, map_subtype_smul_standard_eq_standard] at hg
    set_option backward.isDefEq.respectTransparency false in
      simp only [map_inv, inv_mul_cancel_left] at hg
    have hdist : dist (Lattice.standard R) (cartanDiag ϖ hϖ f • Lattice.standard R) = 0 := by
      simp [hg]
    simp only [cartanDiag_smul_standard] at hdist
    simp only [Lattice.standard] at hdist
    apply_fun Int.ofNat at hdist
    simp only [Int.ofNat_eq_coe, dist_twist _ _ hf, Fin.isValue, CharP.cast_eq_zero, sub_eq_zero] at hdist
    rw [Lattice.ext_iff, Lattice.smul_M] at hg
    simp only [cartanDiag] at hg
    rw [Matrix.GeneralLinearGroup.diagonal_smul _ _ _ (0 : Fin 2)] at hg
    · simp only [Fin.isValue, zpow_neg, Units.smul_mk_apply] at hg
      have : ϖ.val ^ f 0 • (Lattice.standard R).M = (Lattice.standard R).M := hg
      rw [Lattice.standard_M, SetLike.ext'_iff] at this
      simp only [Fin.isValue, Submodule.coe_pointwise_smul, LinearMap.range_coe,
        pow_smul_range_eq_range_iff hϖ] at this
      have : f = 0 := by
        ext i
        fin_cases i
        · simpa
        · simpa [← hdist]
      subst this
      use k₁ * k₂
      set_option backward.isDefEq.respectTransparency false in
        rw [cartanDiag_zero, GL_map_eq, GL_map_eq] at h
      set_option backward.isDefEq.respectTransparency false in
        simpa using h
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [hdist]
  · rintro ⟨k, rfl⟩
    rw [map_subtype_smul_standard_eq_standard]
end BruhatTits
