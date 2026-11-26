-- Prove2me | Theorems.Thm_re_inner_aeval_crouzeixProductRemainderPolynomial_nonneg_of_cauchy_support
-- name    : re_inner_aeval_crouzeixProductRemainderPolynomial_nonneg_of_cauchy_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:34:51.727614+00:00
-- url     : https://prove2.me/theorems/5ee9e65d-3d30-43b6-9fa4-a6868fa79ff5
-- title:
--   re inner aeval crouzeix Product Remainder Polynomial nonneg of cauchy support: re inner aeval crouzeix Product Remainder Polynomial nonneg of cauchy support
-- statement:
--   The evaluated product remainder is accretive: its quadratic real part is
--   nonnegative on every vector.  This is the scalar-form consequence of the
--   positive integrated-variance identity above.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/GeneralSymmetrized.lean#L758-L789
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/GeneralSymmetrized.lean#L758-L789

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

theorem re_inner_aeval_crouzeixProductRemainderPolynomial_nonneg_of_cauchy_support
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
          (w - Omega.boundaryParam t)).re ≤ 0)
    (x : E) :
    0 ≤ RCLike.re ⟪x,
      Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) x⟫_ℂ := by sorry
