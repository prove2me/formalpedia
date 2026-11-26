-- Prove2me | Theorems.Thm_inner_inv_norm_smul_apply
-- name    : inner_inv_norm_smul_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:34:49.359703+00:00
-- url     : https://prove2.me/theorems/9c69ec6e-29c5-482b-b31f-f4a52d29a317
-- title:
--   inner inv norm smul apply: inner inv norm smul apply
-- statement:
--   The inner inv norm smul apply construction uses the inner inv norm smul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Helpers.lean#L89-L97
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Helpers.lean#L89-L97

import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Helpers
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem inner_inv_norm_smul_apply (A : E →L[ℂ] E) {x : E} (hx : x ≠ 0) :
    ⟪((‖x‖ : ℂ)⁻¹) • x, A (((‖x‖ : ℂ)⁻¹) • x)⟫_ℂ =
    ⟪x, A x⟫_ℂ / (‖x‖ : ℂ) ^ 2 := by sorry
