-- Prove2me | Theorems.Thm_circle_center_mem_closure_numericalRange_of_global_polynomial_bound_of_forall_symmetrized_bound
-- name    : circle_center_mem_closure_numericalRange_of_global_polynomial_bound_of_forall_symmetrized_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:58:27.852481+00:00
-- url     : https://prove2.me/theorems/269cfcbc-e55b-5931-91f6-7fbc89b29e9f
-- title:
--   circle center mem closure numerical Range of global polynomial bound of forall symmetrized bound: circle center mem closure numerical Range of global polynomial bound of forall symmetrized bound
-- statement:
--   A finite global polynomial-calculus bound, together with universal sharp
--   symmetrization on an enclosing circle, forces the circle center into the
--   closed numerical range.  No normality or particular value of the finite
--   constant is needed.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L230-L249
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L230-L249

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

theorem circle_center_mem_closure_numericalRange_of_global_polynomial_bound_of_forall_symmetrized_bound
    [Nontrivial E] (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (C : ℝ) (_hC : 0 ≤ C)
    (_hcalc : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q‖ ≤
        C * polynomialSupNorm q (closure (numericalRange A)))
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q (closure (numericalRange A))) :
    c ∈ closure (numericalRange A) := by sorry
