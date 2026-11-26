-- Prove2me | Theorems.Thm_crouzeix_palencia_of_convexThickening_support_boundaryDoubleLayer_automaticMass_automaticWinding_radial_vanishingAtZero
-- name    : crouzeix_palencia_of_convexThickening_support_boundaryDoubleLayer_automaticMass_automaticWinding_radial_vanishingAtZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:05:29.370361+00:00
-- url     : https://prove2.me/theorems/89d65b4b-7ba2-5912-ad67-348441d5358e
-- title:
--   crouzeix palencia of convex Thickening support boundary Double Layer automatic Mass automatic Winding radial vanishing At Zero: crouzeix palencia of convex Thickening support boundary Double Layer aut
-- statement:
--   The numerical-range support condition now supplies both analytic
--   normalizations that were formerly hypotheses: oriented convex winding gives
--   the scalar Cauchy kernel, while affine resolvent homotopy gives the operator
--   resolvent mass.  Only polynomial approximation and auxiliary reproduction
--   remain explicit beyond the exact smooth carrier realization.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureAssembly.lean#L487-L536
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureAssembly.lean#L487-L536

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

theorem crouzeix_palencia_of_convexThickening_support_boundaryDoubleLayer_automaticMass_automaticWinding_radial_vanishingAtZero
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      polynomialSupNorm p (frontier (Omega n).carrier) = 1 →
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
