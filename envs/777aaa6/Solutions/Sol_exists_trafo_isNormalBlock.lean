-- Prove2me | solution 1 for exists_trafo_isNormalBlock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:32:10.126829+00:00
-- url     : https://prove2.me/submissions/9eacb146-b02d-4bb6-a3ac-328007d2681b

import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Mathlib
import Definitions.Def_BruhatTits_Cartan_Existence
import Theorems.Thm_P2M_exists_normalization0__0f257ed9185d
import Theorems.Thm_colEliminator_mul_rowEliminator_lastRow
import Theorems.Thm_colEliminator_mul_rowEliminator_lastCol
import Theorems.Thm_colEliminator_mul_rowEliminator_last_last
import Theorems.Thm_colEliminator_mul_rowEliminator_coeffs_sup
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
theorem _root_.solution (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K) :
    ∃ (k₁ k₂ : GL (Fin k ⊕ Unit) R),
    IsNormalBlock (R := R) ((k₁.val : Matrix _ _ K) * g * (k₂.val : Matrix _ _ K)) ∧
      ((k₁.val : Matrix _ _ K) * g * (k₂.val : Matrix _ _ K)).coeffs_sup v = g.coeffs_sup v := by
  obtain ⟨a, b, hagb, hagbv⟩ := exists_normalization0' (R := R) g
  let g' : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K := a.val * g * b.val
  have hg' : v (g' (Sum.inr ()) (Sum.inr ())) = g'.coeffs_sup v := hagb
  let k₁ := colEliminator g' hg' * a
  let k₂ := b * rowEliminator g' hg'
  use k₁
  use k₂
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · ext j _
    simp only [Units.val_mul, Matrix.map_mul, zero_apply, k₁, k₂]
    convert_to ((colEliminator g' hg').val * g' * (rowEliminator g' hg').val) (Sum.inl j) (Sum.inr ()) = 0
    · simp only [toBlocks₁₂, of_apply, g']
      group
    · apply colEliminator_mul_rowEliminator_lastCol
  · ext _ j
    simp only [Units.val_mul, Matrix.map_mul, zero_apply, k₁, k₂]
    convert_to ((colEliminator g' hg').val * g' * (rowEliminator g' hg').val) (Sum.inr ()) (Sum.inl j) = 0
    · simp only [toBlocks₂₁, of_apply, g']
      group
    · apply colEliminator_mul_rowEliminator_lastRow
  · simp only [Units.val_mul, Matrix.map_mul, k₁, k₂]
    convert_to v (((colEliminator g' hg').val * g' * (rowEliminator g' hg').val) (Sum.inr ()) (Sum.inr ())) =
        ((colEliminator g' hg').val * g' * (rowEliminator g' hg').val).coeffs_sup v
    · simp only [g']
      group
    · simp only [g']
      group
    · rw [colEliminator_mul_rowEliminator_coeffs_sup]
      rwa [colEliminator_mul_rowEliminator_last_last]
  · simp only [Units.val_mul, Matrix.map_mul, k₁, k₂]
    convert_to ((colEliminator g' hg').val * g' * (rowEliminator g' hg').val).coeffs_sup v =
        g.coeffs_sup v
    · simp only [g']
      group
    · rw [colEliminator_mul_rowEliminator_coeffs_sup]
      exact hagbv
