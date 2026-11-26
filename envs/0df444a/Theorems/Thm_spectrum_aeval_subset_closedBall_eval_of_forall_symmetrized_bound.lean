-- Prove2me | Theorems.Thm_spectrum_aeval_subset_closedBall_eval_of_forall_symmetrized_bound
-- name    : spectrum_aeval_subset_closedBall_eval_of_forall_symmetrized_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:58:51.839403+00:00
-- url     : https://prove2.me/theorems/10dc580d-7b5a-5753-8474-abfd1779999d
-- title:
--   spectrum aeval subset closed Ball eval of forall symmetrized bound: spectrum aeval subset closed Ball eval of forall symmetrized bound
-- statement:
--   Equivalently, universal circle symmetrization confines the spectrum of
--   `p(A)` to the disk centered at `p(c)` with radius
--   `sup_K |p - p(c)|`, including the zero-space case.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L419-L449
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L419-L449

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

theorem spectrum_aeval_subset_closedBall_eval_of_forall_symmetrized_bound
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
    spectrum ℂ (Polynomial.aeval A p) ⊆
      Metric.closedBall (Polynomial.eval c p)
        (polynomialSupNorm (p - Polynomial.C (Polynomial.eval c p)) K) := by sorry
