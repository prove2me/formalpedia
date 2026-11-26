-- Prove2me | Theorems.Thm_spectrum_aeval_subset_closedBall_shift_of_mem_of_forall_symmetrized_bound
-- name    : spectrum_aeval_subset_closedBall_shift_of_mem_of_forall_symmetrized_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:44:44.71601+00:00
-- url     : https://prove2.me/theorems/fcaaa83b-7c8e-5269-99f4-615dd67dd4a5
-- title:
--   spectrum aeval subset closed Ball shift of mem of forall symmetrized bound: spectrum aeval subset closed Ball shift of mem of forall symmetrized bound
-- statement:
--   If the circle center belongs to the compact control set, the coupled
--   shifted moments force `spectrum p(A)` into the sharp disk around every scalar
--   `b`, with radius `sup_K |p-b|`.  The proof keeps the shifted scalar power
--   inside the moment and lets its norm be absorbed asymptotically; the zero
--   Hilbert space is handled by its empty spectrum.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L456-L544
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L456-L544

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

theorem spectrum_aeval_subset_closedBall_shift_of_mem_of_forall_symmetrized_bound
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ} (hK : IsCompact K) (hc : c ∈ K)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) (b : ℂ) :
    spectrum ℂ (Polynomial.aeval A p) ⊆
      Metric.closedBall b (polynomialSupNorm (p - Polynomial.C b) K) := by sorry
