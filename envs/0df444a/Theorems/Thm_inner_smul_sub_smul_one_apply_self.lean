-- Prove2me | Theorems.Thm_inner_smul_sub_smul_one_apply_self
-- name    : inner_smul_sub_smul_one_apply_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:34:37.709875+00:00
-- url     : https://prove2.me/theorems/db0c0f9a-0e36-42a7-80e9-4ad105e82f40
-- title:
--   inner smul sub smul one apply self: inner smul sub smul one apply self
-- statement:
--   The inner smul sub smul one apply self construction uses the inner smul sub smul one apply self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Helpers.lean#L55-L60
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Helpers.lean#L55-L60

import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Helpers
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem inner_smul_sub_smul_one_apply_self (c : ℂ) (z₀ : ℂ) (A : E →L[ℂ] E)
    {x : E} (hx : ‖x‖ = 1) :
    ⟪x, (c • (A - z₀ • 1)) x⟫_ℂ = c * (⟪x, A x⟫_ℂ - z₀) := by sorry
