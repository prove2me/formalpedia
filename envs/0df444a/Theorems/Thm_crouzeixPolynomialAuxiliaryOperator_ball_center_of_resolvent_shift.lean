-- Prove2me | Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_center_of_resolvent_shift
-- name    : crouzeixPolynomialAuxiliaryOperator_ball_center_of_resolvent_shift
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:59:28.279606+00:00
-- url     : https://prove2.me/theorems/f712a4c3-0835-4639-84f8-56c3366f896b
-- title:
--   crouzeix Polynomial Auxiliary Operator ball center of resolvent shift: crouzeix Polynomial Auxiliary Operator ball center of resolvent shift
-- statement:
--   The polynomial auxiliary contour on `ball c R` agrees with the centered
--   contour for `A - cI` and the translated polynomial `z ↦ p(z + c)`, provided
--   the corresponding translated-resolvent identity is available.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineAuxiliary.lean#L31-L55
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineAuxiliary.lean#L31-L55

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
set_option autoImplicit false
open Complex MeasureTheory
open scoped InnerProductSpace Interval Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem crouzeixPolynomialAuxiliaryOperator_ball_center_of_resolvent_shift
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ)
    (hshift : ∀ z : ℂ, resolvent (A - c • (1 : E →L[ℂ] E)) z =
      resolvent A (z + c)) :
    crouzeixPolynomialAuxiliaryOperator A (SmoothJordanDomain.ball c R hR) p =
      crouzeixPolynomialAuxiliaryOperator
        (A - c • (1 : E →L[ℂ] E)) (SmoothJordanDomain.ball 0 R hR)
          (p.affineComposition 1 c) := by sorry
