-- Prove2me | Theorems.Thm_crouzeix_palencia_of_convexThickening_cauchy_support_continuous_scalar_companion_approximation
-- name    : crouzeix_palencia_of_convexThickening_cauchy_support_continuous_scalar_companion_approximation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:56:36.634424+00:00
-- url     : https://prove2.me/theorems/0c2ba3ee-88c5-5dce-94df-dba5f4c4d8e3
-- title:
--   crouzeix palencia of convex Thickening cauchy support continuous scalar companion approximation: crouzeix palencia of convex Thickening cauchy support continuous scalar companion approximation
-- statement:
--   The published scalar-companion route with functional-calculus convergence
--   derived rather than assumed.  At every stage, a continuous boundary datum is
--   contractive on the compact control set and uniformly approximated there by
--   polynomials.  The single remaining calculus input is the Plemelj identity
--   saying that its normalized resolvent contour integral is the canonical
--   conjugate-polynomial auxiliary.
--
--   The quantitative contour convergence theorem turns these data into the
--   operator-limit premise of
--   `crouzeix_palencia_of_convexThickening_cauchy_support_contractive_scalar_companion_approximation`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSmoothApproximation.lean#L309-L371
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSmoothApproximation.lean#L309-L371

import Definitions.Def_Operator_Crouzeix_CompactThickeningApprox
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_PalenciaExhaustion
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyMass
import Definitions.Def_Operator_Crouzeix_PolynomialCompanionConvergence
import Definitions.Def_Operator_Crouzeix_PolynomialCompanionNormalization
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem crouzeix_palencia_of_convexThickening_cauchy_support_continuous_scalar_companion_approximation
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
    (hcompanion : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ (g : ℂ → ℂ) (r : ℕ → Polynomial ℂ),
        ContinuousOn g
          ((Omega n).boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) ∧
        (∀ z ∈ compactThickeningApprox (closure (numericalRange A)) n,
          ‖g z‖ ≤ polynomialSupNorm p
            (compactThickeningApprox (closure (numericalRange A)) n)) ∧
        (∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) - g z‖ ≤ 1 / ((j : ℝ) + 1)) ∧
        crouzeixAuxiliaryOperator A (Omega n) g =
          crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
