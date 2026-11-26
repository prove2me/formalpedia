-- Prove2me | Theorems.Thm_norm_sub_adjoint_le_two_mul_numericalRadius
-- name    : norm_sub_adjoint_le_two_mul_numericalRadius
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:27:37.325234+00:00
-- url     : https://prove2.me/theorems/ef6ceb04-e581-45e0-8b76-548f12157376
-- title:
--   norm sub adjoint le two mul numerical Radius: norm sub adjoint le two mul numerical Radius
-- statement:
--   The skew-adjoint numerator `A - A†` has norm at most `2w(A)`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusCartesian.lean#L27-L42
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusCartesian.lean#L27-L42

import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusNormal
import Definitions.Def_Operator_NumericalRange_RadiusCartesian
set_option autoImplicit false
open Complex ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem norm_sub_adjoint_le_two_mul_numericalRadius (A : E →L[ℂ] E) :
    ‖A - A†‖ ≤ 2 * numericalRadius A := by sorry
