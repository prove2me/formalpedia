-- Prove2me | Theorems.Thm_isPositive_add_adjoint_smul_resolvent
-- name    : isPositive_add_adjoint_smul_resolvent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:44:50.193217+00:00
-- url     : https://prove2.me/theorems/f701df7e-9539-4977-90d3-fbd7585c081e
-- title:
--   is Positive add adjoint smul resolvent: is Positive add adjoint smul resolvent
-- statement:
--   The symmetric double-layer kernel is a positive continuous linear map at
--   every supporting point.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayer.lean#L116-L128
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayer.lean#L116-L128

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.InnerProductSpace.Positive
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_Crouzeix_DoubleLayer
set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem isPositive_add_adjoint_smul_resolvent [CompleteSpace E]
    (A : E →L[ℂ] E) {σ ν : ℂ}
    (hW : ∀ w ∈ numericalRange A, ((starRingEnd ℂ) ν * (w - σ)).re ≤ 0) :
    ContinuousLinearMap.IsPositive ((ν • resolvent A σ) +
      ContinuousLinearMap.adjoint (ν • resolvent A σ)) := by sorry
