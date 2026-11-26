-- Prove2me | Theorems.Thm_norm_shifted_aeval_pow_add_shifted_eval_pow_smul_one_le_two_mul_pow_polynomialSupNorm_of_forall_symmetrized_bound
-- name    : norm_shifted_aeval_pow_add_shifted_eval_pow_smul_one_le_two_mul_pow_polynomialSupNorm_of_forall_symmetrized_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:44:28.578957+00:00
-- url     : https://prove2.me/theorems/9ccc9269-773b-5b2c-b7c3-68297c5fef72
-- title:
--   norm shifted aeval pow add shifted eval pow smul one le two mul pow polynomial Sup Norm of forall symmetrized bound: norm shifted aeval pow add shifted eval pow smul one le two mul pow polynomial Sup
-- statement:
--   Universal circle symmetrization preserves the operator/scalar coupling
--   for every positive power after an arbitrary shift `b`.  This is stronger
--   than separately bounding the two summands and retains the cancellation that
--   is relevant to the sharp product problem.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L299-L323
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L299-L323

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

theorem norm_shifted_aeval_pow_add_shifted_eval_pow_smul_one_le_two_mul_pow_polynomialSupNorm_of_forall_symmetrized_bound
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ} (hK : IsCompact K)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) (b : ℂ) (n : ℕ) :
    ‖(Polynomial.aeval A p - b • (1 : E →L[ℂ] E)) ^ (n + 1) +
        (Polynomial.eval c p - b) ^ (n + 1) •
          (1 : E →L[ℂ] E)‖ ≤
      2 * polynomialSupNorm (p - Polynomial.C b) K ^ (n + 1) := by sorry
