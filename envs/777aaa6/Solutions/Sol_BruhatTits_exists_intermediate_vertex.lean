-- Prove2me | solution 1 for BruhatTits.exists_intermediate_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:17:17.181977+00:00
-- url     : https://prove2.me/submissions/9fdb9489-12f8-4550-8862-0105aa9a8033

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Graph_Vertices
import Theorems.Thm_BruhatTits_inv_mk
import Theorems.Thm_BruhatTits_exists_repr_inv
import Theorems.Thm_BruhatTits_dist_smul_GL_eq_dist
import Theorems.Thm_Basis_restrictToLattice_apply
import Theorems.Thm_Basis_restrict_apply
import Theorems.Thm_Basis_smulGL_apply
import Theorems.Thm_Basis_toLinear_symm_ofLinearEquiv_mulVec
import Theorems.Thm_BruhatTits_dist_self
import Theorems.Thm_BruhatTits_dist_symm
import Theorems.Thm_BruhatTits_mulBasisScalar_apply
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_upperTriangularSubgroup_iff
import Theorems.Thm_P2M_Basis_smul__apply_df6e729461ee
import Theorems.Thm_P2M_Basis_swap__apply__280e1e1cec15
import Theorems.Thm_P2M_Basis_swap__apply__cd04b6b0ed1e
import Theorems.Thm_P2M_Basis_swap__symm_e7ab2aa72738
import Theorems.Thm_P2M_Basis_swap_apply__293cd211b0be
import Theorems.Thm_P2M_Basis_swap_apply__dc9b61a54bcb
import Theorems.Thm_P2M_BruhatTits_eq_dist_iff__2efec8b3b981
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
attribute [local simp] BruhatTits.mulBasisScalar_apply
attribute [local simp] GL.coe_map_inv_mul_map
attribute [local simp] GL.coe_map_mul_map_inv
attribute [local simp] GL.map_apply
attribute [local simp] GL.map_inv_mul_map
attribute [local simp] GL.map_mul_map_inv
attribute [local simp] GL.map_one
attribute [local simp] Matrix.BlockTriangular.fin_two_iff
attribute [local simp] Matrix.GeneralLinearGroup.mem_upperTriangularSubgroup_iff
attribute [local simp] P2M_Basis_smul__apply_df6e729461ee
attribute [local simp] P2M_Basis_swap__apply__280e1e1cec15
attribute [local simp] P2M_Basis_swap__apply__cd04b6b0ed1e
attribute [local simp] P2M_Basis_swap__symm_e7ab2aa72738
attribute [local simp] P2M_Basis_swap_apply__293cd211b0be
attribute [local simp] P2M_Basis_swap_apply__dc9b61a54bcb
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


attribute [local simp] BruhatTits.inv_mk
attribute [local simp] BruhatTits.dist_smul_GL_eq_dist

set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
variable {R}
open Pointwise
namespace BruhatTits
theorem _root_.solution (n : ℕ) (x y : Vertices R) (h : inv x y = n + 1) :
    ∃ (o : Vertices R), inv y o = n ∧ inv o x = 1 := by
  obtain ⟨ϖ, hϖ, M', L', bM, bL, rfl, rfl, h0, h1⟩ := exists_repr_inv x y
  rw [h] at h0
  let bT := bM.fromLattice.ntwist₂ hϖ 1 0
  let T : BruhatTits.Lattice R := bT.toLattice
  let bT' : Basis (Fin 2) R T.M := bT.restrictToLattice
  refine ⟨⟦T⟧, ?_, ?_⟩
  · rw [inv_mk, dist_symm, eq_dist_iff₂]
    refine ⟨ϖ, bT', bL, n, 0, hϖ, by simp, ?_, ?_, ?_⟩
    · simp only [h0, bT', bT]
      rw [Basis.restrictToLattice_apply, Basis.ntwist₂_apply₀, Basis.fromLattice_apply, pow_add,
        ← smul_smul, Subring.smul_def, Subring.coe_pow, zpow_natCast]
    · simp only [Fin.isValue, h1, zpow_zero, one_smul, bT', bT, T, Basis.restrictToLattice_apply]
      simp [Basis.ntwist₂_apply₁, Basis.fromLattice_apply]
    · simp
  · show dist T M' = 1
    rw [dist_symm, eq_dist_iff₂]
    refine ⟨ϖ, bM, bT', 1, 0, hϖ, by simp, ?_, ?_, ?_⟩
    · simp only [bT', bT]
      rw [Basis.restrictToLattice_apply, Basis.ntwist₂_apply₀, Basis.fromLattice_apply,
        Subring.smul_def, Subring.coe_pow, zpow_one, pow_one]
    · rw [Basis.restrictToLattice_apply]
      simp [bT', bT, Basis.ntwist₂_apply₁, Basis.fromLattice_apply]
    · simp
end BruhatTits
