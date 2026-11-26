-- Prove2me | Theorems.Thm_norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_le_of_auxiliary_eq_eval_center_smul_one
-- name    : norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_le_of_auxiliary_eq_eval_center_smul_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:02:13.677506+00:00
-- url     : https://prove2.me/theorems/a8734e25-71dc-563b-a5a3-01bd6036d6f8
-- title:
--   norm aeval mul crouzeix Polynomial Auxiliary Operator ball le of auxiliary eq eval center smul one: norm aeval mul crouzeix Polynomial Auxiliary Operator ball le of auxiliary eq eval center smul one
-- statement:
--   On a disk centered at `c`, the scalar auxiliary identity
--   `G = star (p(c)) • 1` implies the sharp L4.2e product estimate.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineProduct.lean#L30-L63
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineProduct.lean#L30-L63

import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_Crouzeix_AffineDisk
import Definitions.Def_Operator_Crouzeix_AffineProduct
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_le_of_auxiliary_eq_eval_center_smul_one
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ ≤ R) (p : Polynomial ℂ)
    (hG : crouzeixPolynomialAuxiliaryOperator A (SmoothJordanDomain.ball c R hR) p =
      star (Polynomial.eval c p) • (1 : E →L[ℂ] E)) :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A (SmoothJordanDomain.ball c R hR) p‖ ≤
      polynomialSupNorm p (Metric.closedBall c R) ^ 2 := by sorry
