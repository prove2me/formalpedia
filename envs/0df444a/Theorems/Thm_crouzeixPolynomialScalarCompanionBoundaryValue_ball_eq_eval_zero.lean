-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_ball_eq_eval_zero
-- name    : crouzeixPolynomialScalarCompanionBoundaryValue_ball_eq_eval_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:48.224142+00:00
-- url     : https://prove2.me/theorems/a91465cc-913f-553b-a8b3-3b44519a9a3d
-- title:
--   crouzeix Polynomial Scalar Companion Boundary Value ball eq eval zero: crouzeix Polynomial Scalar Companion Boundary Value ball eq eval zero
-- statement:
--   The explicit regularized Plemelj value on a centered circle is the
--   conjugate polynomial value at the disk center.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L211-L219
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L211-L219

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionBoundaryValue_ball_eq_eval_zero
    {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ Metric.sphere (0 : ℂ) R) :
    crouzeixPolynomialScalarCompanionBoundaryValue
        (SmoothJordanDomain.ball 0 R hR) p xi =
      star (Polynomial.eval 0 p) := by sorry
