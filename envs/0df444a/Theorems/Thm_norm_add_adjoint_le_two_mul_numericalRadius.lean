-- Prove2me | Theorems.Thm_norm_add_adjoint_le_two_mul_numericalRadius
-- name    : norm_add_adjoint_le_two_mul_numericalRadius
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:27:37.885452+00:00
-- url     : https://prove2.me/theorems/78f2af57-15bf-4a3b-8bc9-ae83ea33cf08
-- title:
--   norm add adjoint le two mul numerical Radius: norm add adjoint le two mul numerical Radius
-- statement:
--   The selfadjoint numerator `A + A†` has norm at most `2w(A)`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusCartesian.lean#L17-L24
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusCartesian.lean#L17-L24

import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusNormal
import Definitions.Def_Operator_NumericalRange_RadiusCartesian
set_option autoImplicit false
open Complex ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem norm_add_adjoint_le_two_mul_numericalRadius (A : E →L[ℂ] E) :
    ‖A + A†‖ ≤ 2 * numericalRadius A := by sorry
