-- Prove2me | Theorems.Thm_numericalRadius_adjoint
-- name    : numericalRadius_adjoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:21:20.669028+00:00
-- url     : https://prove2.me/theorems/ba94035d-06e5-4105-9c6b-37f3ba1a952d
-- title:
--   numerical Radius adjoint: numerical Radius adjoint
-- statement:
--   Numerical radius is invariant under adjoint.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAdjoint.lean#L30-L33
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAdjoint.lean#L30-L33

import Definitions.Def_Operator_NumericalRange_Adjoint
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
set_option autoImplicit false
open Complex
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem numericalRadius_adjoint (A : E →L[ℂ] E) :
    numericalRadius (A†) = numericalRadius A := by sorry
