-- Prove2me | Theorems.Thm_circle_center_mem_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
-- name    : circle_center_mem_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:43:32.533731+00:00
-- url     : https://prove2.me/theorems/d40cd68e-14fa-5c43-bb88-0456cdfeb6bf
-- title:
--   circle center mem of is Compact nonempty convex of forall symmetrized bound: circle center mem of is Compact nonempty convex of forall symmetrized bound
-- statement:
--   Universal sharp symmetrization on an enclosing circle, controlled by a
--   compact nonempty convex set, forces the circle center into that set.  No
--   independent polynomial-calculus bound is needed: if a separator power `B` is
--   close to `-1`, its square is close to `1`, while symmetrization of the squared
--   power would make it close to `-1`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L111-L200
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L111-L200

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

theorem circle_center_mem_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
    [Nontrivial E] (A : E →L[ℂ] E) {K : Set ℂ}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty) (hconvex : Convex ℝ K)
    (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K) :
    c ∈ K := by sorry
