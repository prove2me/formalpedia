-- Prove2me | Theorems.Thm_aeval_C_star_eval_center_eq_crouzeixPolynomialAuxiliaryOperator_ball_center
-- name    : aeval_C_star_eval_center_eq_crouzeixPolynomialAuxiliaryOperator_ball_center
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:22:39.642025+00:00
-- url     : https://prove2.me/theorems/117cd9c7-22b6-4137-9991-b0ce777dddea
-- title:
--   aeval C star eval center eq crouzeix Polynomial Auxiliary Operator ball center: aeval C star eval center eq crouzeix Polynomial Auxiliary Operator ball center
-- statement:
--   The constant polynomial representing the closed disk companion evaluates
--   at `A` to the conjugate-polynomial auxiliary operator.  This is the exact
--   functional-calculus identification behind the disk instance of the published
--   companion route.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L637-L648
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L637-L648

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem aeval_C_star_eval_center_eq_crouzeixPolynomialAuxiliaryOperator_ball_center
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R) (p : Polynomial ℂ) :
    Polynomial.aeval A
        (Polynomial.C (star (Polynomial.eval c p))) =
      crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball c R hR) p := by sorry
