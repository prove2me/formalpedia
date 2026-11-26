-- Prove2me | Theorems.Thm_inner_sub_smul_one_apply_self
-- name    : inner_sub_smul_one_apply_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:34:50.855829+00:00
-- url     : https://prove2.me/theorems/d0b0c302-c92d-486e-aa97-3abe78fd8975
-- title:
--   inner sub smul one apply self: inner sub smul one apply self
-- statement:
--   The inner sub smul one apply self construction uses the inner sub smul one apply self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Helpers.lean#L62-L67
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Helpers.lean#L62-L67

import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Helpers
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem inner_sub_smul_one_apply_self (A : E →L[ℂ] E) (l : ℂ)
    {x : E} (hx : ‖x‖ = 1) :
    ⟪x, (A - l • 1) x⟫_ℂ = ⟪x, A x⟫_ℂ - l := by sorry
