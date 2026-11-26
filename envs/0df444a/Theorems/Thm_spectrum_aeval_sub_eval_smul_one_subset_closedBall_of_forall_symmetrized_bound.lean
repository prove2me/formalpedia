-- Prove2me | Theorems.Thm_spectrum_aeval_sub_eval_smul_one_subset_closedBall_of_forall_symmetrized_bound
-- name    : spectrum_aeval_sub_eval_smul_one_subset_closedBall_of_forall_symmetrized_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:49:04.270545+00:00
-- url     : https://prove2.me/theorems/4d96dd64-4020-4f83-b0f3-d789835719a8
-- title:
--   spectrum aeval sub eval smul one subset closed Ball of forall symmetrized bound: spectrum aeval sub eval smul one subset closed Ball of forall symmetrized bound
-- statement:
--   Universal circle symmetrization alone confines the spectrum of the
--   centered value `p(A) - p(c)I` to the disk whose radius is the sup norm of
--   `p - p(c)` on the compact control set.  No independent global
--   polynomial-calculus estimate is assumed; the zero Hilbert space has empty
--   spectrum.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L356-L414
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L356-L414

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

theorem spectrum_aeval_sub_eval_smul_one_subset_closedBall_of_forall_symmetrized_bound
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ} (hK : IsCompact K)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) :
    spectrum ℂ (Polynomial.aeval A p -
        Polynomial.eval c p • (1 : E →L[ℂ] E)) ⊆
      Metric.closedBall 0
        (polynomialSupNorm (p - Polynomial.C (Polynomial.eval c p)) K) := by sorry
