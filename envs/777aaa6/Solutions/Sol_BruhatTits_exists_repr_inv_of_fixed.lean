-- Prove2me | solution 1 for BruhatTits.exists_repr_inv_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:11:15.358647+00:00
-- url     : https://prove2.me/submissions/33921a1b-7458-4952-9ee3-0e8416775637

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Graph_Vertices
import Theorems.Thm_BruhatTits_inv_mk
import Theorems.Thm_Basis_restrictToLattice_apply
import Theorems.Thm_Basis_restrict_apply
import Theorems.Thm_Basis_smulGL_apply
import Theorems.Thm_Basis_toLinear_symm_ofLinearEquiv_mulVec
import Theorems.Thm_BruhatTits_Lattice_smul_isSimilar
import Theorems.Thm_BruhatTits_dist_self
import Theorems.Thm_BruhatTits_exists_repr_dist
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

set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
variable {R}
open Pointwise
namespace BruhatTits
theorem _root_.solution (M : BruhatTits.Lattice R) (y : Vertices R) :
    ∃ (ϖ : R) (_ : Irreducible ϖ) (L : BruhatTits.Lattice R)
      (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M),
      ⟦L⟧ = y ∧ bL 0 = ϖ ^ (inv ⟦M⟧ y) • (bM 0).val ∧ bL 1 = (bM 1).val := by
  refine Quotient.inductionOn' y (fun L ↦ ?_)
  obtain ⟨ϖ, bM, bL, f, hϖ, _, hrep, hdiff⟩ := exists_repr_dist M L
  have hϖ' : ϖ.val ≠ 0 := by simpa using hϖ.ne_zero
  let L' : BruhatTits.Lattice R := (Units.mk0 ϖ.val hϖ') ^ (- f 1) • L
  let bL' : Basis (Fin 2) R L'.M := mulBasisScalar ((Units.mk0 ϖ.val hϖ') ^ (-f 1)) bL
  refine ⟨ϖ, hϖ, L', bM, bL', ?_, ?_, ?_⟩
  · exact Quotient.sound (Lattice.smul_isSimilar R L _)
  · simp only [bL', hrep 0]
    rw [mulBasisScalar_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0,
      inv_mk, hrep, smul_smul, ← zpow_add₀ hϖ', neg_add_eq_sub, hdiff, R.smul_def, R.coe_pow,
      zpow_natCast]
  · simp only [bL', hrep 1]
    rw [mulBasisScalar_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0, hrep,
      smul_smul, ← zpow_add₀ hϖ', neg_add_eq_sub, sub_self, zpow_zero, one_smul]
end BruhatTits
