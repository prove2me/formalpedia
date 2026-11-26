-- Prove2me | Theorems.Thm_norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_polynomialSupNorm_frontier_of_cauchy_support
-- name    : norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_polynomialSupNorm_frontier_of_cauchy_support
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:50:30.472051+00:00
-- url     : https://prove2.me/theorems/e9a5800c-bc8a-44c6-a7e5-e5f76e937108
-- title:
--   norm aeval add star crouzeix Polynomial Auxiliary Operator le two mul polynomial Sup Norm frontier of cauchy support: norm aeval add star crouzeix Polynomial Auxiliary Operator le two mul polynomial S
-- statement:
--   The generic smooth-domain symmetrized estimate with the canonical
--   boundary constant.  The Cauchy and outward-support inputs imply
--   `‖p(A) + G†‖ ≤ 2 * sup_{z ∈ frontier Ω} ‖p(z)‖`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/GeneralSymmetrized.lean#L794-L817
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/GeneralSymmetrized.lean#L794-L817

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

theorem norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_polynomialSupNorm_frontier_of_cauchy_support
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
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
          (w - Omega.boundaryParam t)).re ≤ 0) :
    ‖Polynomial.aeval A p +
        star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤
      2 * polynomialSupNorm p (frontier Omega.carrier) := by sorry
