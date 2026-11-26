-- Prove2me | Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_add_C
-- name    : crouzeixPolynomialAuxiliaryOperator_add_C
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:52:47.879942+00:00
-- url     : https://prove2.me/theorems/6955ec7a-7a1d-4e14-b1f3-39cf1ea13bd4
-- title:
--   crouzeix Polynomial Auxiliary Operator add C: crouzeix Polynomial Auxiliary Operator add C
-- statement:
--   Adding a constant to a polynomial adds the conjugate scalar identity to
--   its auxiliary operator.  This is the operator counterpart of the exact
--   constant-shift invariance of the product remainder.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductBase.lean#L81-L91
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductBase.lean#L81-L91

import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ProductBase
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem crouzeixPolynomialAuxiliaryOperator_add_C
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ) (a : ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hCauchy : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * Complex.I) • (1 : E →L[ℂ] E)) :
    crouzeixPolynomialAuxiliaryOperator A Omega (p + Polynomial.C a) =
      crouzeixPolynomialAuxiliaryOperator A Omega p +
        star a • (1 : E →L[ℂ] E) := by sorry
