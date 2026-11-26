-- Prove2me | Theorems.Thm_numericalRadius_nonneg
-- name    : numericalRadius_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:02:23.769804+00:00
-- url     : https://prove2.me/theorems/bbd44719-4cda-5715-9ce9-e18f5e6f2b13
-- title:
--   numerical Radius nonneg: numerical Radius nonneg
-- statement:
--   The numerical radius is nonnegative.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Bounded.lean#L55-L57
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Bounded.lean#L55-L57

import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Bounded
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRadius_nonneg (A : E →L[ℂ] E) :
    0 ≤ numericalRadius A := by sorry
