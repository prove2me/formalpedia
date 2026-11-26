-- Prove2me | Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one
-- name    : crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:57:37.301846+00:00
-- url     : https://prove2.me/theorems/4e6b4ed0-be90-4639-947e-c87de511fed6
-- title:
--   crouzeix Polynomial Auxiliary Operator ball eq eval zero smul one: crouzeix Polynomial Auxiliary Operator ball eq eval zero smul one
-- statement:
--   For `‖A‖ < R`, the conjugate-polynomial auxiliary operator on the centered disk is the
--   constant operator `star (p.eval 0) • 1`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleAuxiliary.lean#L27-L102
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleAuxiliary.lean#L27-L102

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
set_option autoImplicit false
open Complex ComplexConjugate Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (p : Polynomial ℂ) :
    crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball 0 R ((norm_nonneg A).trans_lt hR)) p =
      star (Polynomial.eval 0 p) • (1 : E →L[ℂ] E) := by sorry
