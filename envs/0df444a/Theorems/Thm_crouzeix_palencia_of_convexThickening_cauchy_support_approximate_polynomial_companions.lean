-- Prove2me | Theorems.Thm_crouzeix_palencia_of_convexThickening_cauchy_support_approximate_polynomial_companions
-- name    : crouzeix_palencia_of_convexThickening_cauchy_support_approximate_polynomial_companions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:53:25.851059+00:00
-- url     : https://prove2.me/theorems/0e2ddbb6-c48e-503a-bb0f-75925230e4b2
-- title:
--   crouzeix palencia of convex Thickening cauchy support approximate polynomial companions: crouzeix palencia of convex Thickening cauchy support approximate polynomial companions
-- statement:
--   The smooth-stage companion assembly only needs the natural additive-error
--   form of uniform polynomial approximation.  A sequence bounded by
--   `supNorm p + 1 / (j + 1)` is asymptotically rescaled to an exactly contractive
--   one before applying
--   `crouzeix_palencia_of_convexThickening_cauchy_support_tendsto_polynomial_companions`.
--
--   In the nontrivial Hilbert-space case, every compact thickening is infinite.
--   Thus a zero stage sup norm forces `p = 0`, and conjugate linearity makes the
--   canonical auxiliary operator zero, discharging the necessary normalization
--   edge case.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSmoothApproximation.lean#L167-L242
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSmoothApproximation.lean#L167-L242

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

theorem crouzeix_palencia_of_convexThickening_cauchy_support_approximate_polynomial_companions
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
      ∃ r : ℕ → Polynomial ℂ,
        (∀ j, polynomialSupNorm (r j)
            (compactThickeningApprox (closure (numericalRange A)) n) ≤
          polynomialSupNorm p
              (compactThickeningApprox (closure (numericalRange A)) n) +
            1 / ((j : ℝ) + 1)) ∧
        Tendsto (fun j => Polynomial.aeval A (r j)) atTop
          (nhds (crouzeixPolynomialAuxiliaryOperator A (Omega n) p))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
