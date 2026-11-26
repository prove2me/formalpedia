-- Prove2me | Theorems.Thm_contourIntegral_resolvent_eq_two_pi_I_smul_one_of_oriented_convex_carrier_of_nontrivial
-- name    : contourIntegral_resolvent_eq_two_pi_I_smul_one_of_oriented_convex_carrier_of_nontrivial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:42:58.142073+00:00
-- url     : https://prove2.me/theorems/1d75dd83-4ea1-42ee-a704-ccf222a0384f
-- title:
--   contour Integral resolvent eq two pi I smul one of oriented convex carrier of nontrivial: contour Integral resolvent eq two pi I smul one of oriented convex carrier of nontrivial
-- statement:
--   The contour Integral resolvent eq two pi I smul one of oriented convex carrier of nontrivial construction uses the contour Integral resolvent eq two pi I smul one of oriented convex carrier of nontrivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L457-L492
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L457-L492

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

theorem contourIntegral_resolvent_eq_two_pi_I_smul_one_of_oriented_convex_carrier_of_nontrivial
    [Nontrivial E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (c : ℂ) (hc : c ∈ Omega.carrier)
    (hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by sorry
