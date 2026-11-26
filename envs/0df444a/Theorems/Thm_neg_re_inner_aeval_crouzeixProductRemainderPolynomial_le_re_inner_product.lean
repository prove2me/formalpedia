-- Prove2me | Theorems.Thm_neg_re_inner_aeval_crouzeixProductRemainderPolynomial_le_re_inner_product
-- name    : neg_re_inner_aeval_crouzeixProductRemainderPolynomial_le_re_inner_product
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:34:45.852285+00:00
-- url     : https://prove2.me/theorems/dbf79ef2-d4cc-42ca-b59f-34ce5f246f14
-- title:
--   neg re inner aeval crouzeix Product Remainder Polynomial le re inner product: neg re inner aeval crouzeix Product Remainder Polynomial le re inner product
-- statement:
--   In the exact product decomposition, double-layer positivity retains the
--   sign of the cancellation: the real part of `p(A) G_p` is bounded below by
--   minus the real part of the evaluated lower-degree remainder.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/GeneralSymmetrized.lean#L465-L483
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/GeneralSymmetrized.lean#L465-L483

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

theorem neg_re_inner_aeval_crouzeixProductRemainderPolynomial_le_re_inner_product
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hsupport : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
          (w - Omega.boundaryParam t)).re ≤ 0)
    (x : E) :
    -RCLike.re ⟪x,
        Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) x⟫_ℂ ≤
      RCLike.re ⟪x, (Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A Omega p) x⟫_ℂ := by sorry
