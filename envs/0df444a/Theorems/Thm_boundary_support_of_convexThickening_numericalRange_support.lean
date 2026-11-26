-- Prove2me | Theorems.Thm_boundary_support_of_convexThickening_numericalRange_support
-- name    : boundary_support_of_convexThickening_numericalRange_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:23:17.064073+00:00
-- url     : https://prove2.me/theorems/338ce4a5-e3c9-58f6-873e-16f6b7c71242
-- title:
--   boundary support of convex Thickening numerical Range support: boundary support of convex Thickening numerical Range support
-- statement:
--   The existing numerical-range support inequality fixes the orientation of
--   every smooth convex thickening and therefore propagates to all of its
--   frontier points.  Nonemptiness of the smooth carrier forces the numerical
--   range to be nonempty through the exact thickening identity, providing the
--   interior point that selects the normal orientation.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureAssembly.lean#L212-L230
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureAssembly.lean#L212-L230

import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAssembly
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
omit [CompleteSpace E]

theorem boundary_support_of_convexThickening_numericalRange_support
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0) :
    ∀ (n : ℕ) (xi : ℂ), xi ∈ frontier (Omega n).carrier →
      ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (xi - (Omega n).boundaryParam t)).re ≤ 0 := by sorry
