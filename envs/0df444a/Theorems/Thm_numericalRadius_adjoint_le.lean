-- Prove2me | Theorems.Thm_numericalRadius_adjoint_le
-- name    : numericalRadius_adjoint_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:22.291881+00:00
-- url     : https://prove2.me/theorems/007e4586-dfa7-4ed4-89f8-8d8eb962fb58
-- title:
--   numerical Radius adjoint le: numerical Radius adjoint le
-- statement:
--   Taking the adjoint cannot increase the numerical radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAdjoint.lean#L19-L27
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAdjoint.lean#L19-L27

import Definitions.Def_Operator_NumericalRange_Adjoint
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
set_option autoImplicit false
open Complex
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem numericalRadius_adjoint_le (A : E →L[ℂ] E) :
    numericalRadius (A†) ≤ numericalRadius A := by sorry
