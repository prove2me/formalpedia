-- Prove2me | Theorems.Thm_norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le
-- name    : norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:39:49.163031+00:00
-- url     : https://prove2.me/theorems/e482b0ac-c51d-56e1-96bd-31c40dacd3d9
-- title:
--   norm aeval mul crouzeix Polynomial Auxiliary Operator ball center le: norm aeval mul crouzeix Polynomial Auxiliary Operator ball center le
-- statement:
--   **Affine-disk L4.2e product bound.** If `‖A - cI‖ < R`, the actual polynomial auxiliary
--   operator on `ball c R` satisfies the sharp squared sup-norm estimate.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineProduct.lean#L67-L76
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineProduct.lean#L67-L76

import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_Crouzeix_AffineDisk
import Definitions.Def_Operator_Crouzeix_AffineProduct
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R ((norm_nonneg (A - c • 1)).trans_lt hA)) p‖ ≤
      polynomialSupNorm p (Metric.closedBall c R) ^ 2 := by sorry
