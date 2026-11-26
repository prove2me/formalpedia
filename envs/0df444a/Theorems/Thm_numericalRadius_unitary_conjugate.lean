-- Prove2me | Theorems.Thm_numericalRadius_unitary_conjugate
-- name    : numericalRadius_unitary_conjugate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:26:35.015472+00:00
-- url     : https://prove2.me/theorems/9d18009a-b3d7-4748-95fa-03fbe86c7a75
-- title:
--   numerical Radius unitary conjugate: numerical Radius unitary conjugate
-- statement:
--   Numerical radius is invariant under unitary conjugation.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAdjoint.lean#L65-L69
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAdjoint.lean#L65-L69

import Definitions.Def_Operator_NumericalRange_Adjoint
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
set_option autoImplicit false
open Complex
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem numericalRadius_unitary_conjugate (A U : E →L[ℂ] E)
    (hU : U ∈ unitary (E →L[ℂ] E)) :
    numericalRadius (U† * A * U) = numericalRadius A := by sorry
