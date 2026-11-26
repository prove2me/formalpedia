-- Prove2me | Theorems.Thm_re_inner_smul_resolvent_nonneg
-- name    : re_inner_smul_resolvent_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:33:49.869805+00:00
-- url     : https://prove2.me/theorems/ca3cf65b-77ea-59f4-a8bd-9717bd145bc2
-- title:
--   re inner smul resolvent nonneg: re inner smul resolvent nonneg
-- statement:
--   **Double-layer positivity at a supporting point.**  If the numerical range of `A` lies in
--   the closed half-plane `{w | re (conj ν * (w - σ)) ≤ 0}` -- for instance `σ` a boundary point
--   of a convex domain containing `W(A)` and `ν` an outward normal there -- then the quadratic
--   form of `ν • R_A(σ)` has nonnegative real part.  No resolvent-set hypothesis is needed: off
--   the resolvent set Mathlib's `resolvent` is `0` and the form vanishes.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayer.lean#L65-L98
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayer.lean#L65-L98

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.InnerProductSpace.Positive
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_Crouzeix_DoubleLayer
set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem re_inner_smul_resolvent_nonneg (A : E →L[ℂ] E) {σ ν : ℂ}
    (hW : ∀ w ∈ numericalRange A, ((starRingEnd ℂ) ν * (w - σ)).re ≤ 0) (x : E) :
    0 ≤ (⟪x, (ν • resolvent A σ) x⟫_ℂ).re := by sorry
