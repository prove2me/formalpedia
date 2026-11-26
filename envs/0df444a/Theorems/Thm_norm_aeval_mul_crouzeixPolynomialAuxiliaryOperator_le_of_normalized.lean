-- Prove2me | Theorems.Thm_norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_of_normalized
-- name    : norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_of_normalized
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:03:59.2628+00:00
-- url     : https://prove2.me/theorems/740485eb-b358-5640-b48d-22a0545c2eb7
-- title:
--   norm aeval mul crouzeix Polynomial Auxiliary Operator le of normalized: norm aeval mul crouzeix Polynomial Auxiliary Operator le of normalized
-- statement:
--   On an infinite compact set, it suffices to prove the sharp product bound
--   for positive-degree polynomials of unit sup norm.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductNormalization.lean#L24-L69
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductNormalization.lean#L24-L69

import Definitions.Def_Operator_Crouzeix_PolynomialSupNormZero
import Definitions.Def_Operator_Crouzeix_ProductNormalization
set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_of_normalized
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (K : Set ℂ)
    (hK : IsCompact K) (hKinf : K.Infinite) (p : Polynomial ℂ)
    (hp : 0 < p.natDegree)
    (hnormalized : ∀ q : Polynomial ℂ, 0 < q.natDegree →
      polynomialSupNorm q K = 1 →
        ‖Polynomial.aeval A q *
          crouzeixPolynomialAuxiliaryOperator A Omega q‖ ≤ 1) :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
      polynomialSupNorm p K ^ 2 := by sorry
