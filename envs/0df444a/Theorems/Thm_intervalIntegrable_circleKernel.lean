-- Prove2me | Theorems.Thm_intervalIntegrable_circleKernel
-- name    : intervalIntegrable_circleKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:31:52.343864+00:00
-- url     : https://prove2.me/theorems/b9b2fb4d-266f-5b2c-badc-ac31a2e659d0
-- title:
--   interval Integrable circle Kernel: interval Integrable circle Kernel
-- statement:
--   The circle kernel is interval integrable over `[0, 2π]`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleKernel.lean#L76-L80
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleKernel.lean#L76-L80

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

theorem intervalIntegrable_circleKernel (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hρ : Metric.sphere c R ⊆ resolventSet ℂ A) (hR : 0 ≤ R) :
    IntervalIntegrable (fun t : ℝ => (-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t))
      MeasureTheory.volume 0 (2 * Real.pi) := by sorry
