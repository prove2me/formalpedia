-- Prove2me | Theorems.Thm_numericalRange_subset_closedBall
-- name    : numericalRange_subset_closedBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:34:29.538363+00:00
-- url     : https://prove2.me/theorems/7b4adddb-6b61-5b09-996d-cff807556d50
-- title:
--   numerical Range subset closed Ball: numerical Range subset closed Ball
-- statement:
--   The numerical range is contained in the closed disk centered at zero
--   with radius the operator norm.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Bounded.lean#L37-L41
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Bounded.lean#L37-L41

import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Bounded
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRange_subset_closedBall (A : E →L[ℂ] E) :
    numericalRange A ⊆ Metric.closedBall 0 ‖A‖ := by sorry
