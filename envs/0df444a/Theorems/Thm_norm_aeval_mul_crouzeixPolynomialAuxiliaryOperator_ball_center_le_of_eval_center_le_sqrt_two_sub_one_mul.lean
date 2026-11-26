-- Prove2me | Theorems.Thm_norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_eval_center_le_sqrt_two_sub_one_mul
-- name    : norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_eval_center_le_sqrt_two_sub_one_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:01:08.442803+00:00
-- url     : https://prove2.me/theorems/9827148a-3e35-52d2-b5a6-be553cb3c1e2
-- title:
--   norm aeval mul crouzeix Polynomial Auxiliary Operator ball center le of eval center le sqrt two sub one mul: norm aeval mul crouzeix Polynomial Auxiliary Operator ball center le of eval center le sqrt
-- statement:
--   The sharp auxiliary product bound holds without any normality assumption
--   whenever the center value is small: if `|p(c)| ≤ (sqrt 2 - 1) m`, the
--   same-polynomial symmetrized estimate bounds `‖p(A)‖` by `2m + |p(c)|`, and the
--   identity `(sqrt 2 - 1)^2 + 2 (sqrt 2 - 1) = 1` closes the product estimate.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L800-L874
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L800-L874

import Definitions.Def_Operator_Crouzeix_ConvexRunge
import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_NumericalRange_Nonempty
import Definitions.Def_Operator_Crouzeix_NormalProductSymmetrized
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_eval_center_le_sqrt_two_sub_one_mul
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ} (p : Polynomial ℂ)
    (hsymm :
      ‖Polynomial.aeval A p +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) p)‖ ≤
        2 * polynomialSupNorm p K)
    (hsmall : ‖Polynomial.eval c p‖ ≤
      (Real.sqrt 2 - 1) * polynomialSupNorm p K) :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R
            ((norm_nonneg (A - c • 1)).trans_lt hA)) p‖ ≤
      polynomialSupNorm p K ^ 2 := by sorry
