-- Prove2me | Theorems.Thm_continuous_circleKernel_add_adjoint
-- name    : continuous_circleKernel_add_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:56:21.362004+00:00
-- url     : https://prove2.me/theorems/785c9da8-4099-5aac-bab5-c7b04d7b0618
-- title:
--   continuous circle Kernel add adjoint: continuous circle Kernel add adjoint
-- statement:
--   The symmetrized circle kernel `B t + (B t)†` is continuous.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleKernel.lean#L66-L73
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleKernel.lean#L66-L73

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

theorem continuous_circleKernel_add_adjoint (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hρ : Metric.sphere c R ⊆ resolventSet ℂ A) (hR : 0 ≤ R) :
    Continuous (fun t : ℝ =>
      (-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t) +
        ContinuousLinearMap.adjoint ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t))) := by sorry
