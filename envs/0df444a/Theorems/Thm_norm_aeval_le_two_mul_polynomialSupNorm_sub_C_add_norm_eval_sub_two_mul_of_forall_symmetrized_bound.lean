-- Prove2me | Theorems.Thm_norm_aeval_le_two_mul_polynomialSupNorm_sub_C_add_norm_eval_sub_two_mul_of_forall_symmetrized_bound
-- name    : norm_aeval_le_two_mul_polynomialSupNorm_sub_C_add_norm_eval_sub_two_mul_of_forall_symmetrized_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:44:56.171778+00:00
-- url     : https://prove2.me/theorems/81d2cd6b-24b2-582d-a774-a2229ed6c8f3
-- title:
--   norm aeval le two mul polynomial Sup Norm sub C add norm eval sub two mul of forall symmetrized bound: norm aeval le two mul polynomial Sup Norm sub C add norm eval sub two mul of forall symmetrized b
-- statement:
--   Universal circle symmetrization applied to `p - C b` controls `p(A)`
--   after an arbitrary scalar shift.  The symmetrized operator is exactly
--   `p(A) + (p(c) - 2b)I`, giving the displayed quantitative estimate.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L879-L931
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L879-L931

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

theorem norm_aeval_le_two_mul_polynomialSupNorm_sub_C_add_norm_eval_sub_two_mul_of_forall_symmetrized_bound
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ}
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) (b : ℂ) :
    ‖Polynomial.aeval A p‖ ≤
      2 * polynomialSupNorm (p - Polynomial.C b) K +
        ‖Polynomial.eval c p - 2 * b‖ := by sorry
