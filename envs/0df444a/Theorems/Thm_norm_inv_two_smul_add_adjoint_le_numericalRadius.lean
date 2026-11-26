-- Prove2me | Theorems.Thm_norm_inv_two_smul_add_adjoint_le_numericalRadius
-- name    : norm_inv_two_smul_add_adjoint_le_numericalRadius
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:15:43.319815+00:00
-- url     : https://prove2.me/theorems/ec565b1a-1c84-42d1-a6c6-45467299c74f
-- title:
--   norm inv two smul add adjoint le numerical Radius: norm inv two smul add adjoint le numerical Radius
-- statement:
--   The selfadjoint Cartesian part has norm at most the numerical radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusCartesian.lean#L45-L55
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusCartesian.lean#L45-L55

import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusNormal
import Definitions.Def_Operator_NumericalRange_RadiusCartesian
set_option autoImplicit false
open Complex ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem norm_inv_two_smul_add_adjoint_le_numericalRadius
    (A : E →L[ℂ] E) :
    ‖(2 : ℂ)⁻¹ • (A + A†)‖ ≤ numericalRadius A := by sorry
