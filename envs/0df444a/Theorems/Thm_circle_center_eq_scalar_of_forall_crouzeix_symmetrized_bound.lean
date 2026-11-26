-- Prove2me | Theorems.Thm_circle_center_eq_scalar_of_forall_crouzeix_symmetrized_bound
-- name    : circle_center_eq_scalar_of_forall_crouzeix_symmetrized_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:24:42.48164+00:00
-- url     : https://prove2.me/theorems/5962991b-6a7e-4df7-8b43-da0861f5e4db
-- title:
--   circle center eq scalar of forall crouzeix symmetrized bound: circle center eq scalar of forall crouzeix symmetrized bound
-- statement:
--   If the sharp fixed-control-set symmetrized bound holds for every
--   polynomial at the scalar operator `a • 1`, an enclosing circle must be
--   centered at `a`.  Testing with `X - C a` detects any displacement.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductSymmetrizedAlignment.lean#L58-L105
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductSymmetrizedAlignment.lean#L58-L105

import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_ProductSymmetrizedAlignment
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]

theorem circle_center_eq_scalar_of_forall_crouzeix_symmetrized_bound
    (a c : ℂ) {R : ℝ}
    (hA : ‖a • (1 : E →L[ℂ] E) - c • 1‖ < R)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval (a • (1 : E →L[ℂ] E)) q +
          star (crouzeixPolynomialAuxiliaryOperator
            (a • (1 : E →L[ℂ] E))
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (a • (1 : E →L[ℂ] E) - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q
          (closure (numericalRange (a • (1 : E →L[ℂ] E))))) :
    c = a := by sorry
