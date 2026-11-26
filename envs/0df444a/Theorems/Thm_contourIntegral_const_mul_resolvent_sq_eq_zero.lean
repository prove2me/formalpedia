-- Prove2me | Theorems.Thm_contourIntegral_const_mul_resolvent_sq_eq_zero
-- name    : contourIntegral_const_mul_resolvent_sq_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:42:14.568257+00:00
-- url     : https://prove2.me/theorems/dde6e88e-1416-42ef-835a-0606ad229b05
-- title:
--   contour Integral const mul resolvent sq eq zero: contour Integral const mul resolvent sq eq zero
-- statement:
--   The contour Integral const mul resolvent sq eq zero construction uses the contour Integral const mul resolvent sq eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L237-L267
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L237-L267

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
set_option autoImplicit false
open Complex Filter MeasureTheory Metric Set spectrum
open scoped InnerProductSpace Interval Pointwise Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem contourIntegral_const_mul_resolvent_sq_eq_zero
    (B D : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hres : ∀ t : ℝ,
      Omega.boundaryParam t ∈ resolventSet ℂ B) :
    contourIntegral (fun z : ℂ => D * resolvent B z ^ 2)
      Omega.boundaryParam = 0 := by sorry
