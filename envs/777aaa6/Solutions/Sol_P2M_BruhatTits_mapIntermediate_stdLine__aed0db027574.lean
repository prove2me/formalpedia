-- Prove2me | solution 1 for P2M_BruhatTits_mapIntermediate_stdLine__aed0db027574
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:02:53.723177+00:00
-- url     : https://prove2.me/submissions/1e0cc04f-e945-4db2-83fd-2e9d03c171d8

import Definitions.Def_BruhatTits_Lattice_Transvect
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Quotient
import Theorems.Thm_P2M_Basis_toQuotient__apply_64e19fe42c7f
import Theorems.Thm_P2M_Basis_transvectResidue_apply__556496910c93
import Theorems.Thm_P2M_Basis_transvectResidue_apply__d9f90c0bfc03
import Theorems.Thm_BruhatTits_Lattice_mem_mapIntermediate
import Theorems.Thm_Basis_is_linear_comb_of_mem_ntwist
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
set_option synthInstance.maxHeartbeats 100000
namespace BruhatTits
theorem _root_.solution [IsFractionRing R K] (b : Basis (Fin 2) K (Fin 2 → K))
    {ϖ : R} (hϖ : Irreducible ϖ) :
    b.quotientStdLine₁ hϖ = Submodule.span (ResidueField R) { b.toQuotient' (R := R) 0 } := by
  simp only [Basis.quotientStdLine₁, Fin.isValue]
  ext x
  constructor
  · intro hx
    rw [Lattice.mem_mapIntermediate] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    replace hy : y.val ∈ (b.ntwist₂ hϖ 0 1).toSubmodule := hy
    obtain ⟨α, β, hab⟩ := b.is_linear_comb_of_mem_ntwist hϖ y hy
    simp only [pow_zero, Fin.isValue, one_smul, pow_one] at hab
    rw [Submodule.mem_span_singleton]
    use Ideal.Quotient.mk _ α
    rw [hab]
    simp only [Fin.isValue, Basis.toQuotient'_apply, Basis.toLattice_module, map_add, map_smul]
    have : residue R ϖ = 0 := by
      simp only [residue]
      rw [← RingHom.mem_ker]
      erw [Ideal.mk_ker]
      rw [mem_maximalIdeal, mem_nonunits_iff]
      exact hϖ.not_isUnit
    have : β • ϖ • (b.toLattice (R := R)).toQuotient (b.restrict (R := R) 1) = 0 := by
      show β • residue R ϖ • (b.toLattice (R := R)).toQuotient (b.restrict (R := R) 1) = 0
      rw [this]
      simp
    erw [this]
    simp
    rfl
  · intro hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    refine Quotient.inductionOn' a (fun a ↦ ?_)
    rw [Lattice.mem_mapIntermediate]
    refine ⟨a • b.restrictToLattice (R := R) 0, ?_, ?_⟩
    · show _ ∈ Submodule.span R _
      simp only [Basis.toLattice_module, Fin.isValue, SetLike.val_smul]
      apply Submodule.smul_mem
      apply Submodule.subset_span
      use 0
      simp only [Basis.restrictToLattice_apply, Basis.ntwist₂_apply₀, Basis.ntwist₂_apply₁, pow_zero, one_smul]
      exact (Basis.restrictToLattice_apply (R := R) b _).symm
    · simp only [Fin.isValue, Basis.toLattice_module, Basis.restrictToLattice, map_smul]
      rw [Basis.toQuotient'_apply]
      rfl
end BruhatTits
