-- Prove2me | Theorems.Thm_hasDerivAt_contourIntegral_resolvent_affineOperator_of_boundary_subset_resolventSet
-- name    : hasDerivAt_contourIntegral_resolvent_affineOperator_of_boundary_subset_resolventSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:42:27.256845+00:00
-- url     : https://prove2.me/theorems/c8d04e9d-ed21-5c10-9fc5-f8b86ccd4acf
-- title:
--   has Deriv At contour Integral resolvent affine Operator of boundary subset resolvent Set: has Deriv At contour Integral resolvent affine Operator of boundary subset resolvent Set
-- statement:
--   The has Deriv At contour Integral resolvent affine Operator of boundary subset resolvent Set construction uses the has Deriv At contour Integral resolvent affine Operator of boundary subset resolvent Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L208-L225
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L208-L225

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

theorem hasDerivAt_contourIntegral_resolvent_affineOperator_of_boundary_subset_resolventSet
    (B D : E →L[ℂ] E) (Omega : SmoothJordanDomain) (s : ℂ)
    (hres : ∀ t : ℝ,
      Omega.boundaryParam t ∈ resolventSet ℂ (B + s • D)) :
    HasDerivAt
      (fun w : ℂ =>
        contourIntegral (resolvent (B + w • D)) Omega.boundaryParam)
      (contourIntegral
        (fun z : ℂ =>
          resolvent (B + s • D) z * D * resolvent (B + s • D) z)
        Omega.boundaryParam) s := by sorry
