-- Prove2me | Theorems.Thm_intervalIntegrable_eval_smul_circleKernel_add_adjoint
-- name    : intervalIntegrable_eval_smul_circleKernel_add_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:00:07.784959+00:00
-- url     : https://prove2.me/theorems/723fb20f-45f1-4e70-8e5d-019f635ee656
-- title:
--   interval Integrable eval smul circle Kernel add adjoint: interval Integrable eval smul circle Kernel add adjoint
-- statement:
--   The polynomially weighted symmetrized circle kernel is interval integrable over `[0, 2π]`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleKernel.lean#L92-L99
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleKernel.lean#L92-L99

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

theorem intervalIntegrable_eval_smul_circleKernel_add_adjoint (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hρ : Metric.sphere c R ⊆ resolventSet ℂ A) (hR : 0 ≤ R) (p : ℂ[X]) :
    IntervalIntegrable (fun t : ℝ => p.eval (circleMap c R t) •
      ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t) +
        ContinuousLinearMap.adjoint ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t))))
      MeasureTheory.volume 0 (2 * Real.pi) := by sorry
