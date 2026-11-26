-- Prove2me | Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
-- name    : crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:02:05.682109+00:00
-- url     : https://prove2.me/theorems/2a7a9a3f-3632-4351-8f50-749967c36a76
-- title:
--   crouzeix Polynomial Auxiliary Operator ball center eq eval center smul one: crouzeix Polynomial Auxiliary Operator ball center eq eval center smul one
-- statement:
--   If `‖A - cI‖ < R`, the polynomial auxiliary operator on the disk centered at `c` is the
--   constant operator `star (p.eval c) • 1`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineAuxiliary.lean#L72-L81
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineAuxiliary.lean#L72-L81

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
set_option autoImplicit false
open Complex MeasureTheory
open scoped InnerProductSpace Interval Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (p : Polynomial ℂ) :
    crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball c R ((norm_nonneg (A - c • 1)).trans_lt hA)) p =
      star (Polynomial.eval c p) • (1 : E →L[ℂ] E) := by sorry
