-- Prove2me | Theorems.Thm_norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_of_cauchy_support
-- name    : norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_of_cauchy_support
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:50:13.279146+00:00
-- url     : https://prove2.me/theorems/8134272c-3061-4d90-b84c-4b0e87862277
-- title:
--   norm aeval add star crouzeix Polynomial Auxiliary Operator le two mul of cauchy support: norm aeval add star crouzeix Polynomial Auxiliary Operator le two mul of cauchy support
-- statement:
--   **Generic smooth-domain L4.2d bound.**  If the parametrized boundary
--   satisfies the polynomial and resolvent Cauchy identities, its induced outward
--   normal supports the numerical range pointwise, and `‖p‖ ≤ M` on the boundary,
--   then the polynomial auxiliary operator satisfies the sharp symmetrized bound
--   `‖p(A) + G†‖ ≤ 2 * M`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/GeneralSymmetrized.lean#L224-L312
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/GeneralSymmetrized.lean#L224-L312

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_PositiveIntegral
import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
import Definitions.Def_Operator_Crouzeix_SymmetrizedBound
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_of_cauchy_support
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {M : ℝ}
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hCauchyP : Polynomial.aeval A p =
      (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral (fun z => Polynomial.eval z p • resolvent A z)
          Omega.boundaryParam)
    (hCauchyOne : (∫ t in (0 : ℝ)..(2 * Real.pi),
      deriv Omega.boundaryParam t • resolvent A (Omega.boundaryParam t)) =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (hsupport : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
          (w - Omega.boundaryParam t)).re ≤ 0)
    (hM : 0 ≤ M)
    (hp : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ‖Polynomial.eval (Omega.boundaryParam t) p‖ ≤ M) :
    ‖Polynomial.aeval A p +
        star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤ 2 * M := by sorry
