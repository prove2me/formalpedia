-- Prove2me | Theorems.Thm_norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_one_add_sqrt_two_mul_sq_of_forall_symmetrized_bound
-- name    : norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_one_add_sqrt_two_mul_sq_of_forall_symmetrized_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:02:42.788041+00:00
-- url     : https://prove2.me/theorems/7e493496-9954-4073-8d69-083c4cdd3e44
-- title:
--   norm aeval mul crouzeix Polynomial Auxiliary Operator ball center le one add sqrt two mul sq of forall symmetrized bound: norm aeval mul crouzeix Polynomial Auxiliary Operator ball center le one add s
-- statement:
--   For an arbitrary operator, universal sharp symmetrization on an enclosing
--   circle implies an auxiliary product bound with the global
--   `1 + sqrt 2` Crouzeix--Palencia factor.  The universal family first aligns the
--   circle center with the closed numerical range; scalar evaluation is then
--   sharp, while polynomial evaluation uses the unconditional global bound.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L1152-L1206
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean#L1152-L1206

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

theorem norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_one_add_sqrt_two_mul_sq_of_forall_symmetrized_bound
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q (closure (numericalRange A)))
    (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R
            ((norm_nonneg (A - c • 1)).trans_lt hA)) p‖ ≤
      (1 + Real.sqrt 2) *
        polynomialSupNorm p (closure (numericalRange A)) ^ 2 := by sorry
