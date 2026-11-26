-- Prove2me | Theorems.Thm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_add_C
-- name    : aeval_mul_crouzeixPolynomialAuxiliaryOperator_add_C
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:37:31.993646+00:00
-- url     : https://prove2.me/theorems/f36258b4-f35f-4f8f-befa-31e04259fa94
-- title:
--   aeval mul crouzeix Polynomial Auxiliary Operator add C: aeval mul crouzeix Polynomial Auxiliary Operator add C
-- statement:
--   Exact constant-shift expansion of the auxiliary product.  All four
--   terms are retained, so a later quadratic-form argument may choose the
--   centering scalar without discarding cancellation.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductBase.lean#L96-L112
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductBase.lean#L96-L112

import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ProductBase
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem aeval_mul_crouzeixPolynomialAuxiliaryOperator_add_C
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ) (a : ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hCauchy : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * Complex.I) • (1 : E →L[ℂ] E)) :
    Polynomial.aeval A (p + Polynomial.C a) *
        crouzeixPolynomialAuxiliaryOperator A Omega (p + Polynomial.C a) =
      Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p +
        star a • Polynomial.aeval A p +
        a • crouzeixPolynomialAuxiliaryOperator A Omega p +
        (a * star a) • (1 : E →L[ℂ] E) := by sorry
