-- Prove2me | solution 1 for P2M_BruhatTits_Lattice_mapIntermediate_eq_span___4df1650ccb1f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:10:18.643279+00:00
-- url     : https://prove2.me/submissions/4adc595e-6105-4238-8148-162e45197f85

import Definitions.Def_BruhatTits_Lattice_Transvect
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Quotient
import Theorems.Thm_P2M_Basis_transvectResidue_apply__556496910c93
import Theorems.Thm_P2M_Basis_transvectResidue_apply__d9f90c0bfc03
import Theorems.Thm_BruhatTits_Lattice_mapIntermediate_inj_of
import Theorems.Thm_P2M_BruhatTits_mapIntermediate_stdLine__aed0db027574
import Theorems.Thm_BruhatTits_Lattice_mapIntermediate_finrank_eq_one_of
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
import Theorems.Thm_P2M_Basis_ntwist__toSubmodule_le_6698b043c57e
import Theorems.Thm_P2M_Basis_ntwist__toSubmodule_le_ntwist__toSubmodule_dea830e69c76
import Theorems.Thm_P2M_Basis_ntwist__zero_zero_fe200314a2d0
import Theorems.Thm_P2M_Basis_smul__apply_df6e729461ee
import Theorems.Thm_P2M_Basis_smul_ntwist__ee7cf44200ea
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
import Theorems.Thm_Submodule_exists_generator_of_finrank_eq_one_basis
import Theorems.Thm_Submodule_map_subtype_smul
import Theorems.Thm_Subring_coe_det
import Theorems.Thm_Subring_coe_map_inv_mul_map
import Theorems.Thm_Subring_coe_map_mul_map_inv
import Theorems.Thm_Subtype_val_comp_add
import Theorems.Thm_Subtype_val_comp_single
import Theorems.Thm_Subtype_val_comp_smul
import Theorems.Thm_map_subtype_smul_standard_eq_standard
import Theorems.Thm_maximalIdeal_smul_eq_uniformizer_smul
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
namespace Lattice
theorem _root_.solution (b : Basis (Fin 2) K (Fin 2 → K)) (M : BruhatTits.Lattice R)
    {ϖ : R} (hϖ : Irreducible ϖ)
    (h1 : M.M < b.toSubmodule)
    (h2 : ϖ • b.toSubmodule < M.M)
    (h3 : M.M ≠ (b.ntwist₂ hϖ 0 1).toSubmodule) :
    ∃ (α : R), b.toLattice.mapIntermediate M =
      Submodule.span (ResidueField R)
        {α • b.toQuotient' (R := R) 0 + b.toQuotient' (R := R) 1} := by
  let M' : Submodule (ResidueField R) b.toLattice.quotient := b.toLattice.mapIntermediate M
  have ht : M' ≠ Submodule.span (ResidueField ↥R) {b.toQuotient' 0} := by
    rw [← mapIntermediate_stdLine₁ b hϖ]
    intro heq
    apply h3
    have : (b.ntwist₂ hϖ 0 1).toLattice = M := by
      apply b.toLattice.mapIntermediate_inj_of
      · apply b.ntwist₂_toSubmodule_le
      · rw [maximalIdeal_smul_eq_uniformizer_smul _ hϖ, Basis.toLattice_module]
        nth_rw 1 [← b.ntwist₂_zero_zero hϖ]
        rw [b.smul_ntwist₂]
        apply b.ntwist₂_toSubmodule_le_ntwist₂_toSubmodule
        · simp
        · simp
      · apply le_of_lt h1
      · rw [maximalIdeal_smul_eq_uniformizer_smul _ hϖ]
        exact le_of_lt h2
      · exact heq.symm
    rw [← this]
    simp
  have hr : Module.finrank (ResidueField R) M' = 1 :=
    Lattice.mapIntermediate_finrank_eq_one_of hϖ h1 h2
  obtain ⟨a, ha⟩ := Submodule.exists_generator_of_finrank_eq_one_basis
    (b.toQuotient' (R := R)) M' hr ht
  obtain ⟨α, rfl⟩ := Ideal.Quotient.mk_surjective a
  use α
  exact ha
end Lattice
end BruhatTits
