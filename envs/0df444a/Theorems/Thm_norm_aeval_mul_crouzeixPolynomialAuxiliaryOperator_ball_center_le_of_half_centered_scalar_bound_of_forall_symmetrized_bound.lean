-- Prove2me | Theorems.Thm_norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_half_centered_scalar_bound_of_forall_symmetrized_bound
-- name    : norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_half_centered_scalar_bound_of_forall_symmetrized_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:01:55.854988+00:00
-- url     : https://prove2.me/theorems/86395284-d224-5421-bc5a-91c5f8b4c66d
-- title:
--   norm aeval mul crouzeix Polynomial Auxiliary Operator ball center le of half centered scalar bound of forall symmetrized bound: norm aeval mul crouzeix Polynomial Auxiliary Operator ball center le of
-- statement:
--   The midpoint shift `b = p(c) / 2` eliminates the scalar residual in the
--   shifted symmetrization estimate.  Thus the displayed bound on
--   `sup_K |p - p(c)/2|` alone suffices for the literal sharp product.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L1042-L1068
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L1042-L1068

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

theorem norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_half_centered_scalar_bound_of_forall_symmetrized_bound
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ}
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ)
    (hscalar :
      2 * polynomialSupNorm
          (p - Polynomial.C (Polynomial.eval c p / 2)) K *
        ‖Polynomial.eval c p‖ ≤ polynomialSupNorm p K ^ 2) :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R
            ((norm_nonneg (A - c • 1)).trans_lt hA)) p‖ ≤
      polynomialSupNorm p K ^ 2 := by sorry
