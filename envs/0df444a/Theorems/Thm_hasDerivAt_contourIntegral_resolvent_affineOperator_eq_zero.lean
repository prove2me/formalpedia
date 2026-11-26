-- Prove2me | Theorems.Thm_hasDerivAt_contourIntegral_resolvent_affineOperator_eq_zero
-- name    : hasDerivAt_contourIntegral_resolvent_affineOperator_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:42:26.53212+00:00
-- url     : https://prove2.me/theorems/2336d7ec-4877-4d45-a392-1a05fb85d8cb
-- title:
--   has Deriv At contour Integral resolvent affine Operator eq zero: has Deriv At contour Integral resolvent affine Operator eq zero
-- statement:
--   The has Deriv At contour Integral resolvent affine Operator eq zero construction uses the has Deriv At contour Integral resolvent affine Operator eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L288-L315
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L288-L315

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

theorem hasDerivAt_contourIntegral_resolvent_affineOperator_eq_zero
    (B D : E →L[ℂ] E) (Omega : SmoothJordanDomain) (s : ℂ)
    (hBD : Commute B D)
    (hres : ∀ t : ℝ,
      Omega.boundaryParam t ∈ resolventSet ℂ (B + s • D)) :
    HasDerivAt
      (fun w : ℂ =>
        contourIntegral (resolvent (B + w • D)) Omega.boundaryParam)
      0 s := by sorry
