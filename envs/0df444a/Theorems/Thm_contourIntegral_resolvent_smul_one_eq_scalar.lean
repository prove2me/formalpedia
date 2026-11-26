-- Prove2me | Theorems.Thm_contourIntegral_resolvent_smul_one_eq_scalar
-- name    : contourIntegral_resolvent_smul_one_eq_scalar
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:42:44.836672+00:00
-- url     : https://prove2.me/theorems/0897c5a1-7ff7-417c-a139-71fdf77d4e99
-- title:
--   contour Integral resolvent smul one eq scalar: contour Integral resolvent smul one eq scalar
-- statement:
--   The contour Integral resolvent smul one eq scalar construction uses the contour Integral resolvent smul one eq scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L428-L455
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L428-L455

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

theorem contourIntegral_resolvent_smul_one_eq_scalar
    [Nontrivial E] (Omega : SmoothJordanDomain) (c : ℂ)
    (hc : c ∈ Omega.carrier) :
    contourIntegral (resolvent (c • (1 : E →L[ℂ] E)))
        Omega.boundaryParam =
      contourIntegral (fun z : ℂ => (z - c)⁻¹) Omega.boundaryParam •
        (1 : E →L[ℂ] E) := by sorry
