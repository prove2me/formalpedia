-- Prove2me | Theorems.Thm_exists_trafo_isDiag_induction_step
-- name    : exists_trafo_isDiag_induction_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:16:35.700814+00:00
-- url     : https://prove2.me/theorems/e3ebb261-7691-4788-9556-42d0a93f93b7
-- title:
--   exists trafo is Diag induction step: exists trafo is Diag induction step
-- statement:
--   The exists trafo is Diag induction step construction uses the exists trafo is Diag induction step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Cartan/Existence.lean#L499-L558
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Cartan/Existence.lean#L499-L558

import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Mathlib
import Definitions.Def_BruhatTits_Cartan_Existence
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

theorem exists_trafo_isDiag_induction_step (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (ih : ∀ (h : Matrix (Fin k) (Fin k) K), ∃ (k₁ k₂ : GL (Fin k) R),
      IsMonotoneDiag (R := R) ((k₁.val : Matrix _ _ K) * h * (k₂.val : Matrix _ _ K)) ∧
      ((k₁.val : Matrix _ _ K) * h * (k₂.val : Matrix _ _ K)).coeffs_sup v = h.coeffs_sup v) :
    ∃ (k₁ k₂ : GL (Fin k ⊕ Unit) R),
    IsBlockMonotoneDiag (R := R) ((k₁.val : Matrix _ _ K) * g * (k₂.val : Matrix _ _ K)) ∧
      ((k₁.val : Matrix _ _ K) * g * (k₂.val : Matrix _ _ K)).coeffs_sup v = g.coeffs_sup v := by sorry
