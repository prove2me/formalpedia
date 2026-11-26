-- Prove2me | Theorems.Thm_numericalRange_unitary_conjugate
-- name    : numericalRange_unitary_conjugate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:21:23.831855+00:00
-- url     : https://prove2.me/theorems/ab844dde-112c-4071-9e7a-bbe973dbaafc
-- title:
--   numerical Range unitary conjugate: numerical Range unitary conjugate
-- statement:
--   Conjugating an operator by a unitary preserves its numerical range.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAdjoint.lean#L36-L54
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAdjoint.lean#L36-L54

import Definitions.Def_Operator_NumericalRange_Adjoint
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
set_option autoImplicit false
open Complex
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem numericalRange_unitary_conjugate (A U : E →L[ℂ] E)
    (hU : U ∈ unitary (E →L[ℂ] E)) :
    numericalRange (U† * A * U) = numericalRange A := by sorry
