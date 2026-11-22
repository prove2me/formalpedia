-- Prove2me | solution 1 for cartan_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:41:00.435184+00:00
-- url     : https://prove2.me/submissions/cd2b7cfc-7f7d-4b13-81bf-d60d95cfb8cc

import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Mathlib
import Definitions.Def_BruhatTits_Cartan_Existence
import Theorems.Thm_exists_trafo_isDiag
import Theorems.Thm_exists_normalization_of_isMonotoneDiag
import Theorems.Thm_cartanDiag_zero
import Theorems.Thm_conj_cartanDiag_zero_zero
import Theorems.Thm_conj_cartanDiag_one_one
import Theorems.Thm_conj_cartanDiag_one_zero
import Theorems.Thm_conj_cartanDiag_zero_one
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul
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
attribute [local simp] zaddVal_mul
attribute [local simp] zaddVal_units_map


attribute [local simp] cartanDiag_zero
attribute [local simp] conj_cartanDiag_zero_zero
attribute [local simp] conj_cartanDiag_one_one
attribute [local simp] conj_cartanDiag_one_zero
attribute [local simp] conj_cartanDiag_zero_one

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
local notation "v" => ValuationRing.valuation R K
attribute [-simp] Subring.coe_subtype
open Matrix
variable {k l : ℕ+}
noncomputable section
attribute [-simp] Fin.natCast_eq_last Fin.coe_eq_castSucc
set_option maxHeartbeats 300000
variable (ϖ : R) (hϖ : Irreducible ϖ)
theorem _root_.solution [IsDiscreteValuationRing R] (g : GL (Fin k) K) :
    ∃ (k₁ k₂ : GL (Fin k) R) (f : Fin k → ℤ),
      Antitone f ∧ k₁ * g * k₂ = cartanDiag ϖ hϖ f := by
  obtain ⟨k₁', k₂, hk, _⟩ := exists_trafo_isDiag (R := R) g.val
  obtain ⟨d, f, hf, hd⟩ :=
    exists_normalization_of_isMonotoneDiag (R := R) ϖ hϖ
      ((k₁' : GL _ K) * g * (k₂ : GL _ K)) (by simpa using hk)
  refine ⟨(GL.diagonal d) * k₁', k₂, f, hf, ?_⟩
  apply Units.ext
  simp only [GL.map, Units.val_mul, GL.val_diagonal, _root_.map_mul, RingHom.mapMatrix_apply,
    map_zero, diagonal_map, Units.inv_eq_val_inv, _root_.mul_inv_rev, coe_units_inv, val_cartanDiag]
  ext i j
  simp only [mul_assoc, mul_assoc, diagonal_mul, diagonal_apply_eq]
  rw [← mul_assoc]
  by_cases hij : i = j
  · subst hij
    simp only [GL.map, GL.val_diagonal, RingHom.mapMatrix_apply, map_zero, diagonal_map,
      Units.inv_eq_val_inv, coe_units_inv, Units.val_mul, diagonal_mul] at hd
    rw [diagonal_apply_eq]
    exact hd i
  · simp [diagonal_apply_ne _ hij, hk.isDiag hij]
