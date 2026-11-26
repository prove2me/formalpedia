-- Prove2me | Theorems.Thm_norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_centered_polynomialSupNorm_le_sub_of_forall_symmetrized_bound
-- name    : norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_centered_polynomialSupNorm_le_sub_of_forall_symmetrized_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:02:54.351124+00:00
-- url     : https://prove2.me/theorems/115ca28b-5694-4876-990b-5b684af689b5
-- title:
--   norm aeval mul crouzeix Polynomial Auxiliary Operator ball center le of centered polynomial Sup Norm le sub of forall symmetrized bound: norm aeval mul crouzeix Polynomial Auxiliary Operator ball cent
-- statement:
--   The sharp auxiliary product bound also holds without normality in the
--   near-constant regime.  If the sup norm of `p - p(c)` is at most
--   `m - |p(c)|`, universal symmetrization bounds the centered operator by twice
--   that variation, and `(m - |p(c)|)^2 ≥ 0` closes the exact product estimate.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L1109-L1145
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L1109-L1145

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

theorem norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_centered_polynomialSupNorm_le_sub_of_forall_symmetrized_bound
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ}
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ)
    (hcentered : polynomialSupNorm
        (p - Polynomial.C (Polynomial.eval c p)) K ≤
      polynomialSupNorm p K - ‖Polynomial.eval c p‖) :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R
            ((norm_nonneg (A - c • 1)).trans_lt hA)) p‖ ≤
      polynomialSupNorm p K ^ 2 := by sorry
