-- Prove2me | Theorems.Thm_contourIntegral_resolvent_eq_scalar_of_convex_carrier
-- name    : contourIntegral_resolvent_eq_scalar_of_convex_carrier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:42:49.117123+00:00
-- url     : https://prove2.me/theorems/36f16cdc-f553-4e24-a5c9-326a86044250
-- title:
--   contour Integral resolvent eq scalar of convex carrier: contour Integral resolvent eq scalar of convex carrier
-- statement:
--   The contour Integral resolvent eq scalar of convex carrier construction uses the contour Integral resolvent eq scalar of convex carrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L376-L410
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L376-L410

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

theorem contourIntegral_resolvent_eq_scalar_of_convex_carrier
    [Nontrivial E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (c : ℂ) (hc : c ∈ Omega.carrier)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    contourIntegral (resolvent A) Omega.boundaryParam =
      contourIntegral (resolvent (c • (1 : E →L[ℂ] E)))
        Omega.boundaryParam := by sorry
