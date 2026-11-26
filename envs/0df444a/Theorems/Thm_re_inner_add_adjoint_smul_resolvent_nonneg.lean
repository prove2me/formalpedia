-- Prove2me | Theorems.Thm_re_inner_add_adjoint_smul_resolvent_nonneg
-- name    : re_inner_add_adjoint_smul_resolvent_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:36:42.980276+00:00
-- url     : https://prove2.me/theorems/0ec6a8a1-b91c-4cd4-b7ad-09c52a7ad90b
-- title:
--   re inner add adjoint smul resolvent nonneg: re inner add adjoint smul resolvent nonneg
-- statement:
--   The self-adjoint double-layer kernel
--   `nu • R_A(sigma) + (nu • R_A(sigma))†` has nonnegative quadratic form at a
--   supporting point.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayer.lean#L103-L112
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayer.lean#L103-L112

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.InnerProductSpace.Positive
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_Crouzeix_DoubleLayer
set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem re_inner_add_adjoint_smul_resolvent_nonneg [CompleteSpace E]
    (A : E →L[ℂ] E) {σ ν : ℂ}
    (hW : ∀ w ∈ numericalRange A, ((starRingEnd ℂ) ν * (w - σ)).re ≤ 0) (x : E) :
    0 ≤ (⟪x, ((ν • resolvent A σ) +
      ContinuousLinearMap.adjoint (ν • resolvent A σ)) x⟫_ℂ).re := by sorry
