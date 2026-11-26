-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_ball_eq_eval_zero
-- name    : crouzeixPolynomialScalarCompanionClosedExtension_ball_eq_eval_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:52:47.378893+00:00
-- url     : https://prove2.me/theorems/7b3fc135-1d57-4811-ac06-5a21097c8c4a
-- title:
--   crouzeix Polynomial Scalar Companion Closed Extension ball eq eval zero: crouzeix Polynomial Scalar Companion Closed Extension ball eq eval zero
-- statement:
--   The canonical closed extension of the centered-disk companion is the
--   constant `star (p.eval 0)` on the entire closed disk.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L245-L277
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L245-L277

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionClosedExtension_ball_eq_eval_zero
    {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    crouzeixPolynomialScalarCompanionClosedExtension
        (SmoothJordanDomain.ball 0 R hR) p z =
      star (Polynomial.eval 0 p) := by sorry
