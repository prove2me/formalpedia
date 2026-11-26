-- Prove2me | Theorems.Thm_abs_numericalRadius_sub_le_norm
-- name    : abs_numericalRadius_sub_le_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:22:06.525905+00:00
-- url     : https://prove2.me/theorems/2c49d72c-b29b-548c-8b2c-5dab192c0ba0
-- title:
--   abs numerical Radius sub le norm: abs numerical Radius sub le norm
-- statement:
--   Numerical radius changes by at most the operator-norm distance.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Radius.lean#L277-L290
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Radius.lean#L277-L290

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Seminorm
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_NumericalRange_Radius
set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem abs_numericalRadius_sub_le_norm (A B : E →L[ℂ] E) :
    |numericalRadius A - numericalRadius B| ≤ ‖A - B‖ := by sorry
