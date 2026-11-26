-- Prove2me | Theorems.Thm_norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_le
-- name    : norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:33:01.345867+00:00
-- url     : https://prove2.me/theorems/103418af-c3de-4ce2-a9cc-699d818ae471
-- title:
--   norm aeval mul crouzeix Polynomial Auxiliary Operator ball le: norm aeval mul crouzeix Polynomial Auxiliary Operator ball le
-- statement:
--   **Centered-disk L4.2e product bound.**  For `‖A‖ < R`, the actual
--   conjugate-polynomial auxiliary operator on `ball 0 R` satisfies the sharp
--   product estimate.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleProduct.lean#L107-L114
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleProduct.lean#L107-L114

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Definitions.Def_Operator_Crouzeix_CircleProduct
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_le
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball 0 R ((norm_nonneg A).trans_lt hR)) p‖ ≤
      polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) ^ 2 := by sorry
