-- Prove2me | Theorems.Thm_isPositive_add_adjoint_smul_resolvent_circleMap
-- name    : isPositive_add_adjoint_smul_resolvent_circleMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:58:52.772823+00:00
-- url     : https://prove2.me/theorems/72c2cfa0-0824-41bb-bd76-2d5023ec0bce
-- title:
--   is Positive add adjoint smul resolvent circle Map: is Positive add adjoint smul resolvent circle Map
-- statement:
--   The symmetric double-layer kernel along an enclosing circle is a positive
--   continuous linear map.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayer.lean#L173-L187
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayer.lean#L173-L187

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.InnerProductSpace.Positive
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_Crouzeix_DoubleLayer
set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem isPositive_add_adjoint_smul_resolvent_circleMap [CompleteSpace E]
    (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hW : numericalRange A ⊆ Metric.closedBall c R) (t : ℝ) :
    ContinuousLinearMap.IsPositive
      (((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t)) +
        ContinuousLinearMap.adjoint
          ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t))) := by sorry
