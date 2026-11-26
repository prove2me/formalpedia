-- Prove2me | Theorems.Thm_crouzeix_palencia_of_convexThickening_cauchy_support_product
-- name    : crouzeix_palencia_of_convexThickening_cauchy_support_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:37:37.761854+00:00
-- url     : https://prove2.me/theorems/fa56eb19-950a-4d65-9999-7379b1aadd31
-- title:
--   crouzeix palencia of convex Thickening cauchy support product: crouzeix palencia of convex Thickening cauchy support product
-- statement:
--   Suppose the open thickenings of the closed numerical range are realized
--   by smooth Jordan domains whose parametrizations satisfy the polynomial Cauchy
--   identity and whose outward normals support the numerical range.  If the
--   associated auxiliary operators also satisfy the sharp product bound on the
--   closed thickenings for positive-degree polynomials, then the exact
--   Crouzeix--Palencia polynomial spectral-set estimate follows.  Specializing
--   the polynomial identity to `C 1` supplies the resolvent mass identity and,
--   through it, the degree-zero product case.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSmoothApproximation.lean#L381-L463
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSmoothApproximation.lean#L381-L463

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

theorem crouzeix_palencia_of_convexThickening_cauchy_support_product
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
    (hprod : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      ‖Polynomial.aeval A p *
          crouzeixPolynomialAuxiliaryOperator A (Omega n) p‖ ≤
        polynomialSupNorm p
            (compactThickeningApprox (closure (numericalRange A)) n) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
