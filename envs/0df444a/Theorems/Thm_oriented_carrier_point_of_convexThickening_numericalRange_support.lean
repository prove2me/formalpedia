-- Prove2me | Theorems.Thm_oriented_carrier_point_of_convexThickening_numericalRange_support
-- name    : oriented_carrier_point_of_convexThickening_numericalRange_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:19:06.435845+00:00
-- url     : https://prove2.me/theorems/423c3192-1c6f-5dd0-b8ca-d5bb268a3bad
-- title:
--   oriented carrier point of convex Thickening numerical Range support: oriented carrier point of convex Thickening numerical Range support
-- statement:
--   The numerical-range support inequality supplies a point of the open
--   carrier whose canonical-normal sign holds for every real parameter.  The
--   carrier cannot be nonempty unless the underlying numerical range is
--   nonempty; periodicity then extends the fundamental-interval hypothesis.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureAssembly.lean#L174-L204
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureAssembly.lean#L174-L204

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

theorem oriented_carrier_point_of_convexThickening_numericalRange_support
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0) :
    ∀ n, ∃ w ∈ (Omega n).carrier, ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
        (w - (Omega n).boundaryParam t)).re ≤ 0 := by sorry
