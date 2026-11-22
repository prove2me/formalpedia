-- Prove2me | solution 1 for BruhatTits.mapIntermediate_unipotent_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:08:29.568952+00:00
-- url     : https://prove2.me/submissions/e7ab13f3-86fe-424d-8758-0468c8309292

import Definitions.Def_BruhatTits_Lattice_Transvect
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Quotient
import Theorems.Thm_P2M_Basis_transvectResidue_apply__556496910c93
import Theorems.Thm_P2M_Basis_transvectResidue_apply__d9f90c0bfc03
import Theorems.Thm_Basis_unipotentResidue_mk
import Theorems.Thm_BruhatTits_Lattice_mem_mapIntermediate
import Theorems.Thm_Basis_restrictToLattice_apply
import Theorems.Thm_Basis_restrict_apply
import Theorems.Thm_Basis_smulGL_apply
import Theorems.Thm_Basis_toLinear_symm_ofLinearEquiv_mulVec
import Theorems.Thm_Basis_transvectEquiv_mem_of_mem
import Theorems.Thm_Basis_transvectEquiv_symm_mem_of_mem
import Theorems.Thm_Basis_unipotent_mulVec
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_LinearMap_GeneralLinearGroup_coe_ofLinearEquiv_bruhat2024
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_smul
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
attribute [local simp] P2M_Basis_transvectEquiv_apply__a337ed21e963
attribute [local simp] P2M_Basis_transvectEquiv_apply__b7ef14f0fd7c
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
attribute [local simp] map_subtype_smul_standard_eq_standard
attribute [local simp] zaddVal_mul
attribute [local simp] zaddVal_units_map


attribute [local simp] Basis.transvectResidue_apply₀
attribute [local simp] Basis.transvectResidue_apply₁

set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R]
open BruhatTits
set_option synthInstance.maxHeartbeats 30000
open IsLocalRing
set_option synthInstance.maxHeartbeats 50000
set_option maxHeartbeats 500000
open Pointwise
variable [IsFractionRing R K]
namespace BruhatTits
theorem _root_.solution (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) (M : BruhatTits.Lattice R) :
    (b.toLattice (R := R)).mapIntermediate (b.unipotent x • M) =
      ((b.toLattice (R := R)).mapIntermediate M).map (b.unipotentResidue x).toLinearMap := by
  set_option backward.isDefEq.respectTransparency false in
    apply le_antisymm
    · intro x hx
      rw [Lattice.mem_mapIntermediate] at hx
      obtain ⟨y, hymem, rfl⟩ := hx
      rw [Lattice.smul_M, Matrix.GeneralLinearGroup.mem_smul] at hymem
      obtain ⟨m, hm, heq⟩ := hymem
      rw [Basis.unipotent_mulVec] at heq
      have hmL : m ∈ (b.toLattice (R := R)).M := by
        have : m = (b.transvectEquiv x).symm ((b.transvectEquiv x) m) := by simp
        rw [this, heq]
        apply b.transvectEquiv_symm_mem_of_mem
        exact y.property
      let y' : (b.toLattice (R := R)).M := ⟨b.transvectEquiv x m, by
        rw [heq]
        exact y.property⟩
      have : y = y' := by
        ext : 1
        rw [← heq]
      simp only [this, Basis.toLattice_module, Submodule.mem_map, Basis.toLattice_module, y']
      refine ⟨Submodule.Quotient.mk ⟨m, hmL⟩, ?_, ?_⟩
      rw [Lattice.mem_mapIntermediate]
      refine ⟨⟨m, hmL⟩, hm, rfl⟩
      exact Basis.unipotentResidue_mk b x ⟨m, hmL⟩
    · rw [Submodule.map_le_iff_le_comap]
      intro y hy
      rw [(b.toLattice (R := R)).mem_mapIntermediate] at hy
      obtain ⟨m, hmmem, rfl⟩ := hy
      simp only [Basis.toLattice_module, Submodule.mem_comap]
      rw [(b.toLattice (R := R)).mem_mapIntermediate]
      have hmL : b.transvectEquiv x m ∈ (b.toLattice (R := R)).M := by
        apply b.transvectEquiv_mem_of_mem
        exact m.property
      refine ⟨⟨b.transvectEquiv x m, hmL⟩, ?_, ?_⟩
      · rw [Lattice.smul_M, Matrix.GeneralLinearGroup.mem_smul]
        refine ⟨m, hmmem, ?_⟩
        rw [Basis.unipotent_mulVec]
      · erw [Basis.unipotentResidue_mk]
        rfl
end BruhatTits
