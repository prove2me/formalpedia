-- Prove2me | Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_center
-- name    : crouzeixPolynomialAuxiliaryOperator_ball_center
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:59:23.093186+00:00
-- url     : https://prove2.me/theorems/d3e6f735-3472-5c98-9590-a933b5fe835a
-- title:
--   crouzeix Polynomial Auxiliary Operator ball center: crouzeix Polynomial Auxiliary Operator ball center
-- statement:
--   Translating the circle center, the operator, and the polynomial leaves
--   the polynomial auxiliary contour operator unchanged.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineAuxiliary.lean#L59-L66
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineAuxiliary.lean#L59-L66

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
set_option autoImplicit false
open Complex MeasureTheory
open scoped InnerProductSpace Interval Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem crouzeixPolynomialAuxiliaryOperator_ball_center
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) :
    crouzeixPolynomialAuxiliaryOperator A (SmoothJordanDomain.ball c R hR) p =
      crouzeixPolynomialAuxiliaryOperator
        (A - c • (1 : E →L[ℂ] E)) (SmoothJordanDomain.ball 0 R hR)
          (p.affineComposition 1 c) := by sorry
