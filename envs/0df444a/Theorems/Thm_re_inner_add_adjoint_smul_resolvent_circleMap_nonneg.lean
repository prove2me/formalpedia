-- Prove2me | Theorems.Thm_re_inner_add_adjoint_smul_resolvent_circleMap_nonneg
-- name    : re_inner_add_adjoint_smul_resolvent_circleMap_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:36:38.867734+00:00
-- url     : https://prove2.me/theorems/53117391-9aac-56ac-8903-58684dc8386e
-- title:
--   re inner add adjoint smul resolvent circle Map nonneg: re inner add adjoint smul resolvent circle Map nonneg
-- statement:
--   The symmetric double-layer kernel is positive along every enclosing
--   circle, with the outward normal induced by the positive circle orientation.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayer.lean#L159-L169
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayer.lean#L159-L169

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.InnerProductSpace.Positive
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_Crouzeix_DoubleLayer
set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem re_inner_add_adjoint_smul_resolvent_circleMap_nonneg [CompleteSpace E]
    (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hW : numericalRange A ⊆ Metric.closedBall c R) (t : ℝ) (x : E) :
    0 ≤ (⟪x, (((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t)) +
      ContinuousLinearMap.adjoint
        ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t))) x⟫_ℂ).re := by sorry
