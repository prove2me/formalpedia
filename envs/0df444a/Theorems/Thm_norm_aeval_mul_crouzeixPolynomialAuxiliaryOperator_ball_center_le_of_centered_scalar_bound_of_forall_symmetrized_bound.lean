-- Prove2me | Theorems.Thm_norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_centered_scalar_bound_of_forall_symmetrized_bound
-- name    : norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_centered_scalar_bound_of_forall_symmetrized_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:49:31.05627+00:00
-- url     : https://prove2.me/theorems/6872df93-5f81-5ca5-8d46-4f5e77cae0ab
-- title:
--   norm aeval mul crouzeix Polynomial Auxiliary Operator ball center le of centered scalar bound of forall symmetrized bound: norm aeval mul crouzeix Polynomial Auxiliary Operator ball center le of cente
-- statement:
--   Centering `p` gives an adaptive sharp-product criterion without
--   normality.  Universal symmetrization bounds `p(A) - p(c)I` by twice the sup
--   norm of `p - p(c)`; hence the displayed scalar inequality suffices for the
--   literal auxiliary product bound.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L1074-L1103
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L1074-L1103

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

theorem norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_centered_scalar_bound_of_forall_symmetrized_bound
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
      (2 * polynomialSupNorm
          (p - Polynomial.C (Polynomial.eval c p)) K +
        ‖Polynomial.eval c p‖) * ‖Polynomial.eval c p‖ ≤
      polynomialSupNorm p K ^ 2) :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R
            ((norm_nonneg (A - c • 1)).trans_lt hA)) p‖ ≤
      polynomialSupNorm p K ^ 2 := by sorry
