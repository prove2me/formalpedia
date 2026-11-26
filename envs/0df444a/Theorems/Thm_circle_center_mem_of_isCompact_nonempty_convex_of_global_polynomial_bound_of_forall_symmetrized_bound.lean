-- Prove2me | Theorems.Thm_circle_center_mem_of_isCompact_nonempty_convex_of_global_polynomial_bound_of_forall_symmetrized_bound
-- name    : circle_center_mem_of_isCompact_nonempty_convex_of_global_polynomial_bound_of_forall_symmetrized_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:58:49.28485+00:00
-- url     : https://prove2.me/theorems/d10140f5-2939-4ccd-84e5-cb7fbd6121ce
-- title:
--   circle center mem of is Compact nonempty convex of global polynomial bound of forall symmetrized bound: circle center mem of is Compact nonempty convex of global polynomial bound of forall symmetrized
-- statement:
--   A finite polynomial-calculus bound on a compact nonempty convex set,
--   together with universal sharp symmetrization on an enclosing circle controlled
--   by the same set, forces the circle center into that set.  No normality or
--   particular value of the finite constant is needed.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L206-L224
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L206-L224

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

theorem circle_center_mem_of_isCompact_nonempty_convex_of_global_polynomial_bound_of_forall_symmetrized_bound
    [Nontrivial E] (A : E →L[ℂ] E) {K : Set ℂ}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty) (hconvex : Convex ℝ K)
    (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (C : ℝ) (_hC : 0 ≤ C)
    (_hcalc : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q‖ ≤ C * polynomialSupNorm q K)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K) :
    c ∈ K := by sorry
