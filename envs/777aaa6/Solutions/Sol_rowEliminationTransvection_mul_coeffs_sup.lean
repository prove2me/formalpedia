-- Prove2me | solution 1 for rowEliminationTransvection_mul_coeffs_sup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:21:53.184896+00:00
-- url     : https://prove2.me/submissions/11d88f32-6bf0-40d3-b993-b57e3dd35132

import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Mathlib
import Definitions.Def_BruhatTits_Cartan_Existence
import Theorems.Thm_rowEliminationTransvection_mul_same
import Theorems.Thm_rowEliminationTransvection_mul_neq
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_upperTriangularSubgroup_iff
import Theorems.Thm_Matrix_coeffs_sup_le
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
theorem _root_.solution (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffs_sup v) (j : Fin k) :
    g.coeffs_sup v =
      (g * (rowEliminationTransvection g h j).toMatrix).coeffs_sup v := by
  apply le_antisymm
  · rw [← h, ← rowEliminationTransvection_mul_neq h j _ _]
    apply Matrix.coeff_le_coeffs_sup
    exact Sum.inr_ne_inl
  · apply Matrix.coeffs_sup_le
    intro a b
    by_cases he : b = Sum.inl j
    · subst he
      rw [rowEliminationTransvection_mul_same]
      trans
      · apply Valuation.map_add
      · rw [_root_.map_mul, max_le_iff]
        constructor
        · apply Matrix.coeff_le_coeffs_sup
        · have : (ValuationRing.valuation R K) (multFactor g h j) ≤ 1 := by
            simp [← mem_subring_iff_integer, SetLike.coe_mem]
          trans
          apply mul_le_mul' this (by rfl)
          rw [one_mul]
          apply Matrix.coeff_le_coeffs_sup
    · rw [rowEliminationTransvection_mul_neq h j _ _ he]
      apply Matrix.coeff_le_coeffs_sup
