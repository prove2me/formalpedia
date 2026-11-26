-- Prove2me | Theorems.Thm_crouzeix_palencia_of_closure_numericalRange_eq_closedBall
-- name    : crouzeix_palencia_of_closure_numericalRange_eq_closedBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:53:53.81521+00:00
-- url     : https://prove2.me/theorems/b03c687a-e4c5-4640-bc60-904fd8046562
-- title:
--   crouzeix palencia of closure numerical Range eq closed Ball: crouzeix palencia of closure numerical Range eq closed Ball
-- statement:
--   If the closed numerical range is a disk, it is a
--   `(1 + sqrt 2)`-polynomial spectral set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ClosedBallPalencia.lean#L23-L139
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ClosedBallPalencia.lean#L23-L139

import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
import Definitions.Def_Operator_Crouzeix_ClosedBallPalencia
set_option autoImplicit false
open Complex Filter MeasureTheory Metric Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem crouzeix_palencia_of_closure_numericalRange_eq_closedBall
    (A : E →L[ℂ] E) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hW : closure (numericalRange A) = Metric.closedBall c R) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
