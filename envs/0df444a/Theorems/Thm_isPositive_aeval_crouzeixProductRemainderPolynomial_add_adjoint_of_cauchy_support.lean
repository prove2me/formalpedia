-- Prove2me | Theorems.Thm_isPositive_aeval_crouzeixProductRemainderPolynomial_add_adjoint_of_cauchy_support
-- name    : isPositive_aeval_crouzeixProductRemainderPolynomial_add_adjoint_of_cauchy_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:48:57.1658+00:00
-- url     : https://prove2.me/theorems/650df485-e888-453e-863a-4abde1f6bf73
-- title:
--   is Positive aeval crouzeix Product Remainder Polynomial add adjoint of cauchy support: is Positive aeval crouzeix Product Remainder Polynomial add adjoint of cauchy support
-- statement:
--   The Hermitian part of the product remainder is positive.  More
--   precisely, it is the normalized integral of the positive operator-valued
--   variance `(p(z) - p(A))† K(z) (p(z) - p(A))`, where `K` is the
--   double-layer kernel.  This identity retains the coupling between the square
--   auxiliary and the product term; it does not estimate either separately.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/GeneralSymmetrized.lean#L490-L753
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/GeneralSymmetrized.lean#L490-L753

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

theorem isPositive_aeval_crouzeixProductRemainderPolynomial_add_adjoint_of_cauchy_support
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
    ContinuousLinearMap.IsPositive
      (Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) +
        star (Polynomial.aeval A
          (crouzeixProductRemainderPolynomial Omega p))) := by sorry
