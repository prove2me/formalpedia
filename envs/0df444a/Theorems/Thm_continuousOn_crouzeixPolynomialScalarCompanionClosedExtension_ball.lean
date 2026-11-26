-- Prove2me | Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_ball
-- name    : continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:52:22.185719+00:00
-- url     : https://prove2.me/theorems/2718d13b-1384-55f0-9dda-29c4652cd2f4
-- title:
--   continuous On crouzeix Polynomial Scalar Companion Closed Extension ball: continuous On crouzeix Polynomial Scalar Companion Closed Extension ball
-- statement:
--   The canonical scalar-companion extension is continuous on the closed
--   centered disk, now obtained through the regularized Plemelj interface.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L223-L241
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L223-L241

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real

theorem continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_ball
    {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) :
    ContinuousOn
      (crouzeixPolynomialScalarCompanionClosedExtension
        (SmoothJordanDomain.ball 0 R hR) p)
      (Metric.closedBall (0 : ℂ) R) := by sorry
