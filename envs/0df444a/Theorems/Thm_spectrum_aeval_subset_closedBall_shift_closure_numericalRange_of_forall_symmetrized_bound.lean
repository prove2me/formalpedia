-- Prove2me | Theorems.Thm_spectrum_aeval_subset_closedBall_shift_closure_numericalRange_of_forall_symmetrized_bound
-- name    : spectrum_aeval_subset_closedBall_shift_closure_numericalRange_of_forall_symmetrized_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:48:47.18608+00:00
-- url     : https://prove2.me/theorems/dacd258e-e958-5d30-b699-fb2a8fa3209b
-- title:
--   spectrum aeval subset closed Ball shift closure numerical Range of forall symmetrized bound: spectrum aeval subset closed Ball shift closure numerical Range of forall symmetrized bound
-- statement:
--   Universal circle symmetrization controlled by the closed numerical range
--   places `spectrum p(A)` in every disk centered at `b` with radius
--   `sup_{closure W(A)} |p-b|`; the zero Hilbert space has empty spectrum.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L670-L694
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L670-L694

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

theorem spectrum_aeval_subset_closedBall_shift_closure_numericalRange_of_forall_symmetrized_bound
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q (closure (numericalRange A)))
    (p : Polynomial ℂ) (b : ℂ) :
    spectrum ℂ (Polynomial.aeval A p) ⊆
      Metric.closedBall b
        (polynomialSupNorm (p - Polynomial.C b)
          (closure (numericalRange A))) := by sorry
