-- Prove2me | Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_C_eq_star_smul_one
-- name    : crouzeixPolynomialAuxiliaryOperator_C_eq_star_smul_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:48:08.037678+00:00
-- url     : https://prove2.me/theorems/e4663c9d-e82e-58b9-bab3-c8a6eda9b16e
-- title:
--   crouzeix Polynomial Auxiliary Operator C eq star smul one: crouzeix Polynomial Auxiliary Operator C eq star smul one
-- statement:
--   On a contour satisfying the resolvent Cauchy identity, the auxiliary
--   operator for `C a` is `star a • 1`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductBase.lean#L66-L76
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductBase.lean#L66-L76

import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ProductBase
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem crouzeixPolynomialAuxiliaryOperator_C_eq_star_smul_one
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (a : ℂ)
    (hCauchy : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * Complex.I) • (1 : E →L[ℂ] E)) :
    crouzeixPolynomialAuxiliaryOperator A Omega (Polynomial.C a) =
      star a • (1 : E →L[ℂ] E) := by sorry
