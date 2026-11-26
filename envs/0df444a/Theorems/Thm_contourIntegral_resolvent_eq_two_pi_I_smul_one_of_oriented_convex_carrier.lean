-- Prove2me | Theorems.Thm_contourIntegral_resolvent_eq_two_pi_I_smul_one_of_oriented_convex_carrier
-- name    : contourIntegral_resolvent_eq_two_pi_I_smul_one_of_oriented_convex_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:18:31.304359+00:00
-- url     : https://prove2.me/theorems/b4123866-5a8c-5c0d-8025-56d918100a2c
-- title:
--   contour Integral resolvent eq two pi I smul one of oriented convex carrier: contour Integral resolvent eq two pi I smul one of oriented convex carrier
-- statement:
--   Oriented convex geometry computes the operator resolvent contour mass.
--   The subsingleton case is automatic, while in the nontrivial case the affine
--   homotopy joins `A` to the scalar operator at the oriented carrier point.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L497-L512
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L497-L512

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

theorem contourIntegral_resolvent_eq_two_pi_I_smul_one_of_oriented_convex_carrier
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (c : ℂ) (hc : c ∈ Omega.carrier)
    (hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by sorry
