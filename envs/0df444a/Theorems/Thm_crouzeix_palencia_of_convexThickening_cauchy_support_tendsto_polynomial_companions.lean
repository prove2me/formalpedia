-- Prove2me | Theorems.Thm_crouzeix_palencia_of_convexThickening_cauchy_support_tendsto_polynomial_companions
-- name    : crouzeix_palencia_of_convexThickening_cauchy_support_tendsto_polynomial_companions
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:54:51.229944+00:00
-- url     : https://prove2.me/theorems/ab548e6d-9ca2-423f-8da6-e76d755360c4
-- title:
--   crouzeix palencia of convex Thickening cauchy support tendsto polynomial companions: crouzeix palencia of convex Thickening cauchy support tendsto polynomial companions
-- statement:
--   Suppose the open thickenings of the closed numerical range are realized
--   by smooth Jordan domains whose parametrizations satisfy the polynomial Cauchy
--   identity and whose outward normals support the numerical range.  If the
--   canonical Crouzeix auxiliary operator at every stage is the operator-norm
--   limit of polynomials uniformly contractive for the corresponding closed-stage
--   sup norm, then the exact Crouzeix--Palencia estimate follows.
--
--   The all-polynomial Cauchy formula supplies the finite stagewise calculus bound
--   needed to run the fourth-power best-constant bootstrap.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSmoothApproximation.lean#L69-L155
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSmoothApproximation.lean#L69-L155

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

theorem crouzeix_palencia_of_convexThickening_cauchy_support_tendsto_polynomial_companions
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
      ∃ q : ℕ → Polynomial ℂ,
        (∀ j, polynomialSupNorm (q j)
            (compactThickeningApprox (closure (numericalRange A)) n) ≤
          polynomialSupNorm p
            (compactThickeningApprox (closure (numericalRange A)) n)) ∧
        Tendsto (fun j => Polynomial.aeval A (q j)) atTop
          (nhds (crouzeixPolynomialAuxiliaryOperator A (Omega n) p))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
