-- Prove2me | solution 1 for BruhatTits.mem_stabilizer_twist_iff_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:29:57.686563+00:00
-- url     : https://prove2.me/submissions/2724c47f-6846-45a5-bdd7-53b9f92544fd

import Definitions.Def_BruhatTits_Graph_Graph
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Graph_GroupAction
import Theorems.Thm_BruhatTits_cartanDiag_smul_standard
import Theorems.Thm_BruhatTits_stabilizer_smul_standard_eq_map_conj_subtype_range
import Theorems.Thm_Matrix_GL_mem_range_map_iff
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
import Theorems.Thm_GL_map_inv
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_GL_mem_range_map_iff
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
import Theorems.Thm_cartanDiag_inv
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
namespace BruhatTits
theorem _root_.solution {ϖ : R} (hϖ : Irreducible ϖ) (g : GL (Fin 2) R)
    (f : Fin 2 → ℤ) :
    (g : GL (Fin 2) K) ∈ MulAction.stabilizer (GL (Fin 2) K)
      ((Basis.twist (Pi.basisFun K (Fin 2)) hϖ f).toLattice (R := R)) ↔
    ϖ.val ^ (f 1 - f 0) * g 0 1 ∈ R ∧
      ϖ.val ^ (f 0 - f 1) * g 1 0 ∈ R := by
  rw [← cartanDiag_smul_standard, stabilizer_smul_standard_eq_map_conj_subtype_range]
  refine ⟨fun ⟨_, ⟨k, rfl⟩, hk⟩ ↦ ?_, ?_⟩
  · have hk := congr($(hk).val)
    dsimp [- MulAut.conj_apply] at hk
    rw [← Matrix.ext_iff] at hk
    have hne : ϖ.val ≠ 0 := by simp [hϖ.ne_zero]
    refine ⟨?_, ?_⟩
    · have := hk 0 1
      simp only [Fin.isValue, conj_cartanDiag_zero_one, Matrix.GeneralLinearGroup.map_apply,
        Subring.subtype_apply, Matrix.map_apply] at this
      norm_cast at this
      rw [← this, zpow_sub₀ hne, zpow_sub₀ hne]
      ring_nf; field_simp [zpow_ne_zero]
      exact (k.val 0 1).property
    · have := hk 1 0
      simp only [Fin.isValue, conj_cartanDiag_one_zero, Matrix.GeneralLinearGroup.map_apply,
        Subring.subtype_apply, Matrix.map_apply] at this
      norm_cast at this
      rw [← this, zpow_sub₀ hne, zpow_sub₀ hne]
      ring_nf; field_simp [zpow_ne_zero]
      exact (k.val 1 0).property
  · intro ⟨h1, h2⟩
    let k : GL (Fin 2) K := MulAut.conj (cartanDiag ϖ hϖ f)⁻¹ g
    refine ⟨k, ?_, ?_⟩
    · dsimp [k, - MulAut.conj_apply]
      rw [cartanDiag_inv]
      rw [Matrix.GL.mem_range_map_iff R.subtype R.subtype_injective]
      refine ⟨fun i j ↦ ?_, ?_⟩
      · fin_cases i <;> fin_cases j
        · simp [- MulAut.conj_apply]
        · simpa [- MulAut.conj_apply, ← sub_eq_neg_add]
        · simpa [- MulAut.conj_apply, ← sub_eq_neg_add]
        · simp [- MulAut.conj_apply]
      · have : ((g.val).det.val)⁻¹ = g.det.inv.val := by
          change g.det.val.val⁻¹ = (Units.map R.subtype g.det⁻¹).val
          simp [map_inv]
        simp [this]
    · dsimp [k, - MulAut.conj_apply]
      rw [map_inv, MulAut.inv_def, MulEquiv.apply_symm_apply]
end BruhatTits
