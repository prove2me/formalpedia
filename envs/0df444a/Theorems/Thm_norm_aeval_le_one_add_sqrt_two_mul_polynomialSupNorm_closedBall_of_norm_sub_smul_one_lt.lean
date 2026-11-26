-- Prove2me | Theorems.Thm_norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_norm_sub_smul_one_lt
-- name    : norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_norm_sub_smul_one_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:39:01.366892+00:00
-- url     : https://prove2.me/theorems/6cc42fab-5b09-563b-abd2-7b65fc296187
-- title:
--   norm aeval le one add sqrt two mul polynomial Sup Norm closed Ball of norm sub smul one lt: norm aeval le one add sqrt two mul polynomial Sup Norm closed Ball of norm sub smul one lt
-- statement:
--   **Affine-disk Crouzeix--Palencia inequality.** If `A - cI` has norm strictly less than
--   `R`, polynomial evaluation at `A` is bounded by `(1 + √2)` times the polynomial sup-norm
--   on `closedBall c R`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineCrouzeix.lean#L25-L51
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineCrouzeix.lean#L25-L51

import Definitions.Def_Operator_Crouzeix_AffineDisk
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffineCrouzeix
set_option autoImplicit false
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_norm_sub_smul_one_lt
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R) (p : ℂ[X]) :
    ‖Polynomial.aeval A p‖ ≤
      (1 + Real.sqrt 2) * polynomialSupNorm p (Metric.closedBall c R) := by sorry
