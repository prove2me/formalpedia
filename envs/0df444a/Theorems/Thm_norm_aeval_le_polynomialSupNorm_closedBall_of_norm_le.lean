-- Prove2me | Theorems.Thm_norm_aeval_le_polynomialSupNorm_closedBall_of_norm_le
-- name    : norm_aeval_le_polynomialSupNorm_closedBall_of_norm_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:00:18.553662+00:00
-- url     : https://prove2.me/theorems/f4ce9ea9-d06a-4593-b82f-3a864238df2e
-- title:
--   norm aeval le polynomial Sup Norm closed Ball of norm le: norm aeval le polynomial Sup Norm closed Ball of norm le
-- statement:
--   Von Neumann's inequality scaled from the unit disk to a centered disk:
--   if `‖A‖ ≤ R` and `0 < R`, then polynomial evaluation at `A` is bounded by
--   the polynomial sup norm on `closedBall 0 R`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleProduct.lean#L40-L67
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleProduct.lean#L40-L67

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

theorem norm_aeval_le_polynomialSupNorm_closedBall_of_norm_le
    (A : E →L[ℂ] E) {R : ℝ} (hR : 0 < R) (hA : ‖A‖ ≤ R)
    (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p‖ ≤
      polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) := by sorry
