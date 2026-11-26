-- Prove2me | Theorems.Thm_norm_pow_aeval_le_two_mul_pow_polynomialSupNorm_of_eval_eq_zero_of_forall_symmetrized_bound
-- name    : norm_pow_aeval_le_two_mul_pow_polynomialSupNorm_of_eval_eq_zero_of_forall_symmetrized_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:58:32.637505+00:00
-- url     : https://prove2.me/theorems/bcd1c066-17a4-5fba-99f6-22f41a475219
-- title:
--   norm pow aeval le two mul pow polynomial Sup Norm of eval eq zero of forall symmetrized bound: norm pow aeval le two mul pow polynomial Sup Norm of eval eq zero of forall symmetrized bound
-- statement:
--   Universal circle symmetrization makes the functional calculus uniformly
--   power-bounded on the ideal of polynomials vanishing at the circle center.  If
--   `p(c) = 0`, every positive power of `p(A)` has norm at most twice the
--   corresponding power of the sup norm on the compact control set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L273-L293
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L273-L293

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

theorem norm_pow_aeval_le_two_mul_pow_polynomialSupNorm_of_eval_eq_zero_of_forall_symmetrized_bound
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ} (hK : IsCompact K)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) (hpc : Polynomial.eval c p = 0) (n : ℕ) :
    ‖Polynomial.aeval A p ^ (n + 1)‖ ≤
      2 * polynomialSupNorm p K ^ (n + 1) := by sorry
