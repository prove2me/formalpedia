-- Prove2me | Theorems.Thm_crouzeix_palencia_of_convexThickening_cauchy_support_boundaryDoubleLayerDensity_radial_vanishingAtZero
-- name    : crouzeix_palencia_of_convexThickening_cauchy_support_boundaryDoubleLayerDensity_radial_vanishingAtZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:23:42.88528+00:00
-- url     : https://prove2.me/theorems/d88ee845-ad70-4ce5-9c70-3acd5f054ae4
-- title:
--   crouzeix palencia of convex Thickening cauchy support boundary Double Layer Density radial vanishing At Zero: crouzeix palencia of convex Thickening cauchy support boundary Double Layer Density radial
-- statement:
--   The strongest radial scalar-companion capstone with sharp phase
--   contractivity supplied by the explicit boundary double-layer probability
--   measure.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureAssembly.lean#L50-L107
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureAssembly.lean#L50-L107

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

theorem crouzeix_palencia_of_convexThickening_cauchy_support_boundaryDoubleLayerDensity_radial_vanishingAtZero
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hCauchyP : ∀ (p : Polynomial ℂ) (n : ℕ),
      Polynomial.aeval A p =
        (2 * (Real.pi : ℂ) * I)⁻¹ •
          contourIntegral
            (fun z => Polynomial.eval z p • resolvent A z)
            (Omega n).boundaryParam)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (hkernel : ∀ (n : ℕ) (z : ℂ), z ∈ (Omega n).carrier →
      crouzeixScalarCauchyKernel (Omega n) z = 1)
    (hrho : ∀ (n : ℕ) (xi : ℂ),
      xi ∈ frontier (Omega n).carrier →
      IntervalIntegrable
        (crouzeixBoundaryDoubleLayerDensity (Omega n) xi)
        volume 0 (2 * Real.pi))
    (hmass : ∀ (n : ℕ) (xi : ℂ),
      xi ∈ frontier (Omega n).carrier →
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        crouzeixBoundaryDoubleLayerDensity (Omega n) xi t) = 1)
    (hboundarySupport : ∀ (n : ℕ) (xi : ℂ),
      xi ∈ frontier (Omega n).carrier →
      ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (xi - (Omega n).boundaryParam t)).re ≤ 0)
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
