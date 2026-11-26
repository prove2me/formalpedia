-- Prove2me | Theorems.Thm_numericalRadius_le_norm
-- name    : numericalRadius_le_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:02:34.934561+00:00
-- url     : https://prove2.me/theorems/606ff1fd-749b-5759-98ff-d6a077f130dc
-- title:
--   numerical Radius le norm: numerical Radius le norm
-- statement:
--   The numerical radius is bounded above by the operator norm.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Bounded.lean#L74-L79
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Bounded.lean#L74-L79

import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Bounded
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRadius_le_norm (A : E →L[ℂ] E) :
    numericalRadius A ≤ ‖A‖ := by sorry
