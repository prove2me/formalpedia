-- Prove2me | solution 1 for P2M_cartan_decomposition_unique__6facbe8d407d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:26:24.117189+00:00
-- url     : https://prove2.me/submissions/3d488833-df6f-4bda-b3d5-2e95608919ae

import Definitions.Def_BruhatTits_Cartan_Existence
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Cartan_Uniqueness
import Theorems.Thm_P2M_cartan_decomposition_unique__aux_3e99e4a3d7c4
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv
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



set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
variable {k : ℕ+}
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
variable {ϖ : R} {hϖ : Irreducible ϖ}
theorem _root_.solution {k₁ k₂ k₁' k₂' : GL (Fin k) R}
    {f f' : Fin k → ℤ}
    (h : k₁ * cartanDiag ϖ hϖ f * k₂ = k₁' * cartanDiag ϖ hϖ f' * k₂') :
    ∃ σ : Equiv.Perm (Fin k), f ∘ σ = f' := by
  let a : GL (Fin k) R := k₂ * k₂'⁻¹
  let x : GL (Fin k) R := k₁⁻¹ * k₁'
  apply cartan_decomposition_unique'_aux x a f f' (ϖ := ϖ) (hϖ := hϖ)
  simp only [x, a]
  rw [GL.map_mul, GL.map_mul, ← mul_assoc]
  calc _ =
    (GL.map R.subtype k₁)⁻¹ * (k₁ * cartanDiag ϖ hϖ f * k₂) * k₂'⁻¹ * (cartanDiag ϖ hϖ f')⁻¹
      := by group
    _ = (GL.map R.subtype k₁)⁻¹ * k₁' * cartanDiag ϖ hϖ f' * k₂' * k₂'⁻¹ * (cartanDiag ϖ hϖ f')⁻¹
      := by rw [h]; group
    _ = k₁⁻¹ * k₁' * cartanDiag ϖ hϖ f' * k₂' * (GL.map R.subtype k₂')⁻¹ * (cartanDiag ϖ hϖ f')⁻¹
      := by rw [GL.map_inv, GL.map_inv]
    _ = k₁⁻¹ * k₁' := by group
