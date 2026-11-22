-- Prove2me | solution 1 for P2M_BruhatTits_IsStandardNeighbour_exists_unipotent_smul_eq_ntwist__b2043a99b21d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:18:58.777823+00:00
-- url     : https://prove2.me/submissions/578084e8-8a87-425c-9350-1df4b0e627d0

import Definitions.Def_BruhatTits_Graph_Vertices
import Definitions.Def_BruhatTits_Lattice_Quotient
import Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
import Definitions.Def_BruhatTits_Utils_List
import Definitions.Def_BruhatTits_Graph_Edges
import Theorems.Thm_List_smul_lattice_length
import Theorems.Thm_Basis_restrictToLattice_apply
import Theorems.Thm_Basis_restrict_apply
import Theorems.Thm_Basis_smulGL_apply
import Theorems.Thm_Basis_toLinear_symm_ofLinearEquiv_mulVec
import Theorems.Thm_BruhatTits_Lattice_mapIntermediate_inj_of
import Theorems.Thm_BruhatTits_dist_self
import Theorems.Thm_BruhatTits_dist_smul_GL_eq_dist
import Theorems.Thm_BruhatTits_inv_mk
import Theorems.Thm_BruhatTits_mulBasisScalar_apply
import Theorems.Thm_BruhatTits_scalar_smul_GL_smul
import Theorems.Thm_BruhatTits_smul_GL_mono
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
import Theorems.Thm_P2M_Basis_ntwist__ntwist__3af1a375203b
import Theorems.Thm_P2M_Basis_ntwist__toSubmodule_le_ntwist__toSubmodule_dea830e69c76
import Theorems.Thm_P2M_Basis_smul__apply_df6e729461ee
import Theorems.Thm_P2M_Basis_smul_ntwist__ee7cf44200ea
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
import Theorems.Thm_P2M_Basis_unipotentResidue_apply__346093b846ed
import Theorems.Thm_P2M_Basis_unipotentResidue_apply__d6e564de5d3b
import Theorems.Thm_P2M_BruhatTits_Lattice_mapIntermediate_eq_span___4df1650ccb1f
import Theorems.Thm_P2M_BruhatTits_mapIntermediate_stdLine__5e26b89614ae
import Theorems.Thm_P2M_BruhatTits_mapIntermediate_unipotent_smul__55e18c93491a
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
import Theorems.Thm_map_subtype_smul_standard_eq_standard
import Theorems.Thm_maximalIdeal_smul_eq_uniformizer_smul
import Theorems.Thm_unipotent_pow_irred_smul_eq_submodule
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


attribute [local simp] List.smul_lattice_length

set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K] {R : Subring K}
open BruhatTits
open Pointwise
open IsLocalRing
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
namespace BruhatTits
namespace IsStandardNeighbour
theorem _root_.solution {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ)
    (M : BruhatTits.Lattice R) (b : Basis (Fin 2) K (Fin 2 → K))
    (h : IsStandardNeighbour M (b.ntwist₂ hϖ (n + 1) 0).toLattice)
    (hne : ϖ • (b.ntwist₂ hϖ n 0).toSubmodule ≠ M.M) :
    ∃ (x : R), b.unipotent (ϖ ^ (n + 1) * x) • M = (b.ntwist₂ hϖ (n + 2) 0).toLattice := by
  set_option backward.isDefEq.respectTransparency false in
    let L : BruhatTits.Lattice R := (b.ntwist₂ hϖ (n + 1) 0).toLattice
    let κ := ResidueField R
    let M' : Submodule κ L.quotient := L.mapIntermediate M
    let ϖL' : Submodule κ L.quotient :=
      L.mapIntermediate (b.ntwist₂ hϖ (n + 1) 1).toLattice
    have : M' ≠ ϖL' := by
      intro heq
      apply hne
      have : (b.ntwist₂ hϖ (n + 1) 1).toLattice = M := by
        refine L.mapIntermediate_inj_of _ _ ?_ ?_ (le_of_lt h.1) ?_ heq.symm
        · simp only [Basis.toLattice_module, L]
          exact b.ntwist₂_toSubmodule_le_ntwist₂_toSubmodule _ le_rfl zero_le_one
        · simp only [maximalIdeal_smul_eq_uniformizer_smul _ hϖ, Basis.toLattice_module, L,
            b.smul_ntwist₂]
          exact b.ntwist₂_toSubmodule_le_ntwist₂_toSubmodule _ (Nat.le_succ _) le_rfl
        · rw [maximalIdeal_smul_eq_uniformizer_smul _ hϖ]
          exact le_of_lt (h.2 _ hϖ)
      simp only [← this, Basis.toLattice_module, L, b.smul_ntwist₂]
    have hT : L.mapIntermediate ((b.ntwist₂ hϖ (n + 2) 0).toLattice (R := R)) =
        Submodule.span κ { (b.ntwist₂ hϖ (n + 1) 0).toQuotient' (R := R) 1 } := by
      have : b.ntwist₂ hϖ (n + 2) 0 = (b.ntwist₂ hϖ (n + 1) 0).ntwist₂ hϖ 1 0 := by
        rw [b.ntwist₂_ntwist₂]
      rw [this]
      apply mapIntermediate_stdLine₀ (b.ntwist₂ hϖ (n + 1) 0) hϖ
    have ha : ∃ (α : R),
        M' = Submodule.span κ { α • (b.ntwist₂ hϖ (n + 1) 0).toQuotient' (R := R) 0 +
          (b.ntwist₂ hϖ (n + 1) 0).toQuotient' (R := R) 1 } := by
      refine Lattice.mapIntermediate_eq_span'' _ _ hϖ h.1 (h.2 _ hϖ) fun heq ↦ hne ?_
      rw [b.smul_ntwist₂]
      rw [b.ntwist₂_ntwist₂] at heq
      exact heq.symm
    obtain ⟨α, ha⟩ := ha
    use (- α)
    have huniL : b.unipotent (ϖ ^ (n + 1) * (- α)) • L.M = L.M := by
      simp only [L]
      apply unipotent_pow_irred_smul_eq_submodule
      simp
    apply L.mapIntermediate_inj_of
    · rw [← huniL]
      exact smul_GL_mono _ (le_of_lt h.1)
    · rw [Lattice.smul_M, ← huniL, maximalIdeal_smul_eq_uniformizer_smul _ hϖ, Subring.smul_def,
        scalar_smul_GL_smul]
      exact smul_GL_mono _ (le_of_lt <| h.2 _ hϖ)
    · simp [L]
      apply b.ntwist₂_toSubmodule_le_ntwist₂_toSubmodule _ (by simp) le_rfl
    · rw [maximalIdeal_smul_eq_uniformizer_smul _ hϖ]
      simp only [Basis.toLattice_module, L, b.smul_ntwist₂]
      exact b.ntwist₂_toSubmodule_le_ntwist₂_toSubmodule _ le_rfl zero_le_one
    · rw [mapIntermediate_unipotent_smul']
      show Submodule.map _ M' = _
      rw [ha, LinearMap.map_span]
      simp only [Fin.isValue, Set.image_singleton, map_add, LinearMapClass.map_smul]
      show Submodule.span _ _ = _
      erw [LinearMap.CompatibleSMul.map_smul]
      simp only [LinearEquiv.coe_coe, LinearEquiv.coe_toLinearMap]
      rw [Basis.unipotentResidue_apply₁]
      rw [Basis.unipotentResidue_apply₀]
      simpa using hT.symm
end IsStandardNeighbour
end BruhatTits
