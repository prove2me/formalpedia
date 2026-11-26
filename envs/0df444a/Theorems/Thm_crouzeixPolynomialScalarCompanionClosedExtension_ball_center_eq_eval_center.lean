-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_ball_center_eq_eval_center
-- name    : crouzeixPolynomialScalarCompanionClosedExtension_ball_center_eq_eval_center
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:14:45.172676+00:00
-- url     : https://prove2.me/theorems/960b4db8-ecd7-5672-b26a-1c4abb92eb22
-- title:
--   crouzeix Polynomial Scalar Companion Closed Extension ball center eq eval center: crouzeix Polynomial Scalar Companion Closed Extension ball center eq eval center
-- statement:
--   The canonical closed extension of the companion on `ball c R` is the
--   constant `star (p.eval c)` throughout `closedBall c R`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L496-L531
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L496-L531

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionClosedExtension_ball_center_eq_eval_center
    (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Metric.closedBall c R) :
    crouzeixPolynomialScalarCompanionClosedExtension
        (SmoothJordanDomain.ball c R hR) p z =
      star (Polynomial.eval c p) := by sorry
