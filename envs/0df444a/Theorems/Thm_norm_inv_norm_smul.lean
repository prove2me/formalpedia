-- Prove2me | Theorems.Thm_norm_inv_norm_smul
-- name    : norm_inv_norm_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:33:22.853453+00:00
-- url     : https://prove2.me/theorems/9e6518e1-be23-43e1-99a8-8b9f1e7faff2
-- title:
--   norm inv norm smul: norm inv norm smul
-- statement:
--   The norm inv norm smul construction uses the norm inv norm smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Helpers.lean#L13-L16
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Helpers.lean#L13-L16

import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Helpers
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_inv_norm_smul {x : E} (hx : x ≠ 0) :
    ‖((‖x‖ : ℂ)⁻¹) • x‖ = 1 := by sorry
