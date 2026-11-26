-- Prove2me | Theorems.Thm_continuous_resolvent_circleMap
-- name    : continuous_resolvent_circleMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:58:51.969285+00:00
-- url     : https://prove2.me/theorems/a5dab42b-bfa9-5001-86b2-93e6873c232a
-- title:
--   continuous resolvent circle Map: continuous resolvent circle Map
-- statement:
--   The resolvent is continuous along a circle contained in the resolvent set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleKernel.lean#L47-L53
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleKernel.lean#L47-L53

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_Crouzeix_CircleKernel
set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem continuous_resolvent_circleMap (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hρ : Metric.sphere c R ⊆ resolventSet ℂ A) (hR : 0 ≤ R) :
    Continuous (fun t : ℝ => resolvent A (circleMap c R t)) := by sorry
