-- Prove2me | Theorems.Thm_continuous_circleKernel
-- name    : continuous_circleKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:56:20.849511+00:00
-- url     : https://prove2.me/theorems/e30a891c-3749-45c7-aa61-d70b14ff7e46
-- title:
--   continuous circle Kernel: continuous circle Kernel
-- statement:
--   The double-layer circle kernel `B t = (-i γ'(t)) • R_A(γ(t))`, `γ = circleMap c R`, is
--   continuous when the circle lies in the resolvent set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleKernel.lean#L57-L63
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleKernel.lean#L57-L63

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

theorem continuous_circleKernel (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hρ : Metric.sphere c R ⊆ resolventSet ℂ A) (hR : 0 ≤ R) :
    Continuous (fun t : ℝ => (-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t)) := by sorry
