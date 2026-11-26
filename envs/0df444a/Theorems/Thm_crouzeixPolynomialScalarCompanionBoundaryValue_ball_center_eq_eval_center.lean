-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_ball_center_eq_eval_center
-- name    : crouzeixPolynomialScalarCompanionBoundaryValue_ball_center_eq_eval_center
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:53.924305+00:00
-- url     : https://prove2.me/theorems/2cce740c-0962-5ab9-ae04-ba6b5d388f67
-- title:
--   crouzeix Polynomial Scalar Companion Boundary Value ball center eq eval center: crouzeix Polynomial Scalar Companion Boundary Value ball center eq eval center
-- statement:
--   The explicit Plemelj value on an arbitrary circle is the conjugate
--   polynomial value at its center.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L460-L470
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L460-L470

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionBoundaryValue_ball_center_eq_eval_center
    (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ Metric.sphere c R) :
    crouzeixPolynomialScalarCompanionBoundaryValue
        (SmoothJordanDomain.ball c R hR) p xi =
      star (Polynomial.eval c p) := by sorry
