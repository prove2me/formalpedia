-- Prove2me | Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_ball_center_eq
-- name    : crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_ball_center_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:22:04.00743+00:00
-- url     : https://prove2.me/theorems/9a0f1a5b-5bb6-5d55-a183-9b9483773828
-- title:
--   crouzeix Auxiliary Operator scalar Companion Closed Extension ball center eq: crouzeix Auxiliary Operator scalar Companion Closed Extension ball center eq
-- statement:
--   On a disk containing the operator in norm, feeding the canonical closed
--   scalar companion to the auxiliary contour gives exactly the usual
--   conjugate-polynomial auxiliary operator.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L541-L587
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L541-L587

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

theorem crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_ball_center_eq
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R) (p : Polynomial ℂ) :
    crouzeixAuxiliaryOperator A (SmoothJordanDomain.ball c R hR)
        (crouzeixPolynomialScalarCompanionClosedExtension
          (SmoothJordanDomain.ball c R hR) p) =
      crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball c R hR) p := by sorry
