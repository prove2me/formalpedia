-- Prove2me | Theorems.Thm_hasDerivAt_contourIntegral_resolvent_affineOperator
-- name    : hasDerivAt_contourIntegral_resolvent_affineOperator
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:42:04.268324+00:00
-- url     : https://prove2.me/theorems/06a1bf61-abd0-464c-b866-cfeff4683e27
-- title:
--   has Deriv At contour Integral resolvent affine Operator: has Deriv At contour Integral resolvent affine Operator
-- statement:
--   The has Deriv At contour Integral resolvent affine Operator construction uses the has Deriv At contour Integral resolvent affine Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L35-L119
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L35-L119

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

theorem hasDerivAt_contourIntegral_resolvent_affineOperator
    (B D : E →L[ℂ] E) (Omega : SmoothJordanDomain) (s : ℂ)
    {epsilon C : ℝ} (hepsilon : 0 < epsilon) (hC : 0 ≤ C)
    (hres : ∀ w ∈ ball s epsilon, ∀ t : ℝ,
      Omega.boundaryParam t ∈ resolventSet ℂ (B + w • D))
    (hbound : ∀ w ∈ ball s epsilon, ∀ t : ℝ,
      ‖resolvent (B + w • D) (Omega.boundaryParam t)‖ ≤ C) :
    HasDerivAt
      (fun w : ℂ =>
        contourIntegral (resolvent (B + w • D)) Omega.boundaryParam)
      (contourIntegral
        (fun z : ℂ =>
          resolvent (B + s • D) z * D * resolvent (B + s • D) z)
        Omega.boundaryParam) s := by sorry
