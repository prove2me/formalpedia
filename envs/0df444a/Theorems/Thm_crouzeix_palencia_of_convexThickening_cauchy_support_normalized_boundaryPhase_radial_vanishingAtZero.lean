-- Prove2me | Theorems.Thm_crouzeix_palencia_of_convexThickening_cauchy_support_normalized_boundaryPhase_radial_vanishingAtZero
-- name    : crouzeix_palencia_of_convexThickening_cauchy_support_normalized_boundaryPhase_radial_vanishingAtZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:20:06.356093+00:00
-- url     : https://prove2.me/theorems/5ae68806-d7fa-44e6-a7ca-d1e00ca9269f
-- title:
--   crouzeix palencia of convex Thickening cauchy support normalized boundary Phase radial vanishing At Zero: crouzeix palencia of convex Thickening cauchy support normalized boundary Phase radial vanishi
-- statement:
--   Constant-shift invariance reduces approximation to positive-degree
--   polynomials vanishing at zero.  Scaling invariance further restricts contour
--   reproduction to that subclass at frontier sup norm one; the sharp phase input
--   is likewise normalized to frontier sup norm one.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L702-L784
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L702-L784

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem crouzeix_palencia_of_convexThickening_cauchy_support_normalized_boundaryPhase_radial_vanishingAtZero
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
    (hphaseNormalized : ∀ (n : ℕ) (p : Polynomial ℂ),
      0 < p.natDegree →
      polynomialSupNorm p (frontier (Omega n).carrier) = 1 →
      CrouzeixBoundaryPhaseContractive (Omega n) p)
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
