-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_ball_center_boundary_eq
-- name    : crouzeixPolynomialScalarCompanionRegularized_ball_center_boundary_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:14:40.372428+00:00
-- url     : https://prove2.me/theorems/670a1431-e773-5f60-b0a4-531a0ddf063b
-- title:
--   crouzeix Polynomial Scalar Companion Regularized ball center boundary eq: crouzeix Polynomial Scalar Companion Regularized ball center boundary eq
-- statement:
--   On an arbitrary circle, the cancelled transform at a boundary point is
--   the difference between the conjugate polynomial values at the center and at
--   that boundary point.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L308-L419
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L308-L419

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionRegularized_ball_center_boundary_eq
    (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ Metric.sphere c R) :
    crouzeixPolynomialScalarCompanionRegularized
        (SmoothJordanDomain.ball c R hR) p xi xi =
      star (Polynomial.eval c p) - star (Polynomial.eval xi p) := by sorry
