-- Prove2me | Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_ball_center
-- name    : continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_ball_center
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:57.437836+00:00
-- url     : https://prove2.me/theorems/45c4cacd-7e69-5a78-93c2-cba2729fb17d
-- title:
--   continuous On crouzeix Polynomial Scalar Companion Closed Extension ball center: continuous On crouzeix Polynomial Scalar Companion Closed Extension ball center
-- statement:
--   The canonical scalar-companion extension is continuous on every closed
--   disk.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L474-L492
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L474-L492

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real

theorem continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_ball_center
    (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) :
    ContinuousOn
      (crouzeixPolynomialScalarCompanionClosedExtension
        (SmoothJordanDomain.ball c R hR) p)
      (Metric.closedBall c R) := by sorry
