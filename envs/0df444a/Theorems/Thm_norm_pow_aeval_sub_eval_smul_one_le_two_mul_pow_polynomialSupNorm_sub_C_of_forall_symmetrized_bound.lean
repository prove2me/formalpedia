-- Prove2me | Theorems.Thm_norm_pow_aeval_sub_eval_smul_one_le_two_mul_pow_polynomialSupNorm_sub_C_of_forall_symmetrized_bound
-- name    : norm_pow_aeval_sub_eval_smul_one_le_two_mul_pow_polynomialSupNorm_sub_C_of_forall_symmetrized_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:47:59.163969+00:00
-- url     : https://prove2.me/theorems/515b457e-64ee-5a29-95b7-daef6a1708ca
-- title:
--   norm pow aeval sub eval smul one le two mul pow polynomial Sup Norm sub C of forall symmetrized bound: norm pow aeval sub eval smul one le two mul pow polynomial Sup Norm sub C of forall symmetrized b
-- statement:
--   Universal circle symmetrization uniformly power-bounds the centered
--   functional calculus.  For every polynomial `p`, positive powers of
--   `p(A) - p(c)I` are controlled by twice the corresponding power of the sup
--   norm of `p - p(c)` on the compact control set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L329-L349
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L329-L349

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

theorem norm_pow_aeval_sub_eval_smul_one_le_two_mul_pow_polynomialSupNorm_sub_C_of_forall_symmetrized_bound
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ} (hK : IsCompact K)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) (n : ℕ) :
    ‖(Polynomial.aeval A p -
        Polynomial.eval c p • (1 : E →L[ℂ] E)) ^ (n + 1)‖ ≤
      2 * polynomialSupNorm
        (p - Polynomial.C (Polynomial.eval c p)) K ^ (n + 1) := by sorry
