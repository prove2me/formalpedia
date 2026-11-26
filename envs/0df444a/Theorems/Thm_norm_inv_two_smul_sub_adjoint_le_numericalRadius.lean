-- Prove2me | Theorems.Thm_norm_inv_two_smul_sub_adjoint_le_numericalRadius
-- name    : norm_inv_two_smul_sub_adjoint_le_numericalRadius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:15:44.497742+00:00
-- url     : https://prove2.me/theorems/29ab337f-3840-4223-af3e-7bc3cec4a871
-- title:
--   norm inv two smul sub adjoint le numerical Radius: norm inv two smul sub adjoint le numerical Radius
-- statement:
--   The skew-adjoint Cartesian part has norm at most the numerical radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusCartesian.lean#L58-L68
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusCartesian.lean#L58-L68

import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusNormal
import Definitions.Def_Operator_NumericalRange_RadiusCartesian
set_option autoImplicit false
open Complex ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem norm_inv_two_smul_sub_adjoint_le_numericalRadius
    (A : E →L[ℂ] E) :
    ‖(2 : ℂ)⁻¹ • (A - A†)‖ ≤ numericalRadius A := by sorry
