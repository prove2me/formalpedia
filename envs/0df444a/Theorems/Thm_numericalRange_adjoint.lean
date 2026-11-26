-- Prove2me | Theorems.Thm_numericalRange_adjoint
-- name    : numericalRange_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:13.06797+00:00
-- url     : https://prove2.me/theorems/87e3d0f9-f7a4-43ec-9536-077764b71a46
-- title:
--   numerical Range adjoint: numerical Range adjoint
-- statement:
--   The numerical range of the adjoint is the pointwise complex conjugate of
--   the numerical range.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Adjoint.lean#L23-L33
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Adjoint.lean#L23-L33

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Adjoint
set_option autoImplicit false
open scoped InnerProductSpace
open ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem numericalRange_adjoint (A : E →L[ℂ] E) :
    numericalRange (ContinuousLinearMap.adjoint A) =
      (starRingEnd ℂ) '' (numericalRange A) := by sorry
