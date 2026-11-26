-- Prove2me | Theorems.Thm_re_inner_smul_resolvent_circleMap_nonneg
-- name    : re_inner_smul_resolvent_circleMap_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:36:35.862994+00:00
-- url     : https://prove2.me/theorems/3fa04d91-4e0c-52f9-9829-42e23f5368cd
-- title:
--   re inner smul resolvent circle Map nonneg: re inner smul resolvent circle Map nonneg
-- statement:
--   The circle instance: on the positively oriented circle `circleMap c R` the contour kernel
--   direction is `ν = -I * deriv (circleMap c R) t = R • exp (t I)`, an outward normal, so the
--   quadratic form of `ν • R_A(circleMap c R t)` has nonnegative real part whenever `W(A)` lies in
--   the closed disk.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayer.lean#L134-L155
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayer.lean#L134-L155

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.InnerProductSpace.Positive
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_Crouzeix_DoubleLayer
set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem re_inner_smul_resolvent_circleMap_nonneg (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hW : numericalRange A ⊆ Metric.closedBall c R) (t : ℝ) (x : E) :
    0 ≤ (⟪x, ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t)) x⟫_ℂ).re := by sorry
