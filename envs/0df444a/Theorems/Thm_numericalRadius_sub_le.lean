-- Prove2me | Theorems.Thm_numericalRadius_sub_le
-- name    : numericalRadius_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:22:22.650701+00:00
-- url     : https://prove2.me/theorems/655a8993-be18-5242-9e09-7efbf96be9c2
-- title:
--   numerical Radius sub le: numerical Radius sub le
-- statement:
--   Numerical radius satisfies the triangle inequality for subtraction.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Radius.lean#L261-L265
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Radius.lean#L261-L265

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Seminorm
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_NumericalRange_Radius
set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRadius_sub_le (A B : E →L[ℂ] E) :
    numericalRadius (A - B) ≤ numericalRadius A + numericalRadius B := by sorry
