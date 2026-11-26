-- Prove2me | Theorems.Thm_norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_polynomialSupNorm_sq_of_natDegree_eq_zero
-- name    : norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_polynomialSupNorm_sq_of_natDegree_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:53:04.437504+00:00
-- url     : https://prove2.me/theorems/35b3a27c-9324-4b09-a969-a1296e117ffe
-- title:
--   norm aeval mul crouzeix Polynomial Auxiliary Operator le polynomial Sup Norm sq of nat Degree eq zero: norm aeval mul crouzeix Polynomial Auxiliary Operator le polynomial Sup Norm sq of nat Degree eq
-- statement:
--   **Sharp L4.2e base case.**  A degree-zero polynomial satisfies the
--   auxiliary product bound on every nonempty control set, provided the smooth
--   contour has the resolvent Cauchy mass identity.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductBase.lean#L117-L139
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductBase.lean#L117-L139

import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ProductBase
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_polynomialSupNorm_sq_of_natDegree_eq_zero
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ) {K : Set ℂ} (hK : K.Nonempty) (hp : p.natDegree = 0)
    (hCauchy : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * Complex.I) • (1 : E →L[ℂ] E)) :
    ‖Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
      polynomialSupNorm p K ^ 2 := by sorry
