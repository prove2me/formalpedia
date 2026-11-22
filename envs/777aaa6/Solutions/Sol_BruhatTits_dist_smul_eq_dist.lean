-- Prove2me | solution 1 for BruhatTits.dist_smul_eq_dist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:02:21.791182+00:00
-- url     : https://prove2.me/submissions/a5681df4-ee8c-47a8-bb1f-ee5f0c9e1e8a

import Definitions.Def_BruhatTits_Cartan_Uniqueness
import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Lattice_Distance
import Theorems.Thm_BruhatTits_eq_dist_iff
import Theorems.Thm_BruhatTits_exists_repr_dist
import Theorems.Thm_BruhatTits_dist_self
import Theorems.Thm_BruhatTits_mulBasisScalar_apply
import Theorems.Thm_BruhatTits_unit_smul_eq
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_upperTriangularSubgroup_iff
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
import Theorems.Thm_zaddVal_mul
import Theorems.Thm_zaddVal_units_map
attribute [local simp] GL.coe_map_inv_mul_map
attribute [local simp] GL.coe_map_mul_map_inv
attribute [local simp] GL.map_apply
attribute [local simp] GL.map_inv_mul_map
attribute [local simp] GL.map_mul_map_inv
attribute [local simp] GL.map_one
attribute [local simp] Matrix.BlockTriangular.fin_two_iff
attribute [local simp] Matrix.GeneralLinearGroup.mem_upperTriangularSubgroup_iff
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
attribute [local simp] zaddVal_mul
attribute [local simp] zaddVal_units_map


attribute [local simp] BruhatTits.dist_self
attribute [local simp] BruhatTits.mulBasisScalar_apply

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]
open Algebra BruhatTits Matrix GeneralLinearGroup
variable {k : ℕ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
open BruhatTits
open Pointwise
omit [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K]
variable [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K]
namespace BruhatTits
theorem _root_.solution (M L : BruhatTits.Lattice R) (a : Kˣ) :
    dist (a • M) L = dist M L := by
  obtain ⟨ϖ, bM, bL, f, hϖ, hf, hrep, hdiff⟩ := exists_repr_dist M L
  obtain ⟨n, u, ha⟩ := eq_unit_mul_pow_irreducible' ϖ hϖ a
  have h0 : ϖ.val ≠ 0 := by simpa using hϖ.ne_zero
  have : a • M = (Units.mk0 ϖ.val h0) ^ n • M := by
    rw [ha, mul_comm, ← smul_smul, unit_smul_eq]
  rw [this]
  rw [mul_comm] at ha
  have : ϖ.val ^ n ≠ 0 := by
    apply zpow_ne_zero
    simpa using hϖ.ne_zero
  let bM' : Basis (Fin 2) R ((Units.mk0 ϖ.val h0) ^ n • M).M :=
    mulBasisScalar ((Units.mk0 ϖ.val h0) ^ n) bM
  have hbM' (i : Fin 2) : ϖ.val ^ (-n) • (bM' i).val = bM i := by
    simp only [bM', mulBasisScalar_apply]
    simp only [_root_.zpow_neg, Units.val_zpow_eq_zpow_val, Units.val_mk0, smul_smul]
    field_simp
    simp only [one_smul]
  let f' (i : Fin 2) : ℤ := f i + (-n)
  rw [eq_dist_iff]
  use ϖ, bM', bL, f', hϖ
  refine ⟨?_, ?_, ?_⟩
  · apply hf.add_const
  · intro i
    simp only [Lattice.smul_module, f']
    rw [zpow_add₀]
    rw [← smul_smul]
    erw [hbM' i]
    exact hrep i
    simp only [ne_eq, ZeroMemClass.coe_eq_zero]
    exact hϖ.ne_zero
  · simp [f', hdiff]
end BruhatTits
