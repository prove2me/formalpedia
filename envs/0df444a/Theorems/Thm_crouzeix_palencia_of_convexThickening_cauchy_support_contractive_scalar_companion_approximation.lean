-- Prove2me | Theorems.Thm_crouzeix_palencia_of_convexThickening_cauchy_support_contractive_scalar_companion_approximation
-- name    : crouzeix_palencia_of_convexThickening_cauchy_support_contractive_scalar_companion_approximation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:53:39.348848+00:00
-- url     : https://prove2.me/theorems/ab0f4380-2026-4d3b-895b-190e9d95159d
-- title:
--   crouzeix palencia of convex Thickening cauchy support contractive scalar companion approximation: crouzeix palencia of convex Thickening cauchy support contractive scalar companion approximation
-- statement:
--   The published companion route in scalar analytic form.  At every smooth
--   stage, suppose an interior scalar companion `g` is bounded by the stage sup
--   norm of `p`, is uniformly approximated there by polynomials `r j` with error
--   `1 / (j + 1)`, and those polynomial evaluations converge at `A` to the
--   canonical contour auxiliary.  Then the exact Crouzeix--Palencia estimate
--   follows.
--
--   This theorem leaves precisely the analytic companion contraction, polynomial
--   approximation, and functional-calculus identification as explicit inputs; the
--   additive-to-exact normalization and fourth-power bootstrap are internal.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSmoothApproximation.lean#L254-L296
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSmoothApproximation.lean#L254-L296

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

theorem crouzeix_palencia_of_convexThickening_cauchy_support_contractive_scalar_companion_approximation
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
        (∀ z ∈ compactThickeningApprox (closure (numericalRange A)) n,
          ‖g z‖ ≤ polynomialSupNorm p
            (compactThickeningApprox (closure (numericalRange A)) n)) ∧
        (∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) - g z‖ ≤ 1 / ((j : ℝ) + 1)) ∧
        Tendsto (fun j => Polynomial.aeval A (r j)) atTop
          (nhds (crouzeixPolynomialAuxiliaryOperator A (Omega n) p))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
