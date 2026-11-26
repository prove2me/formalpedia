-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_ball_boundary_eq
-- name    : crouzeixPolynomialScalarCompanionRegularized_ball_boundary_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:14:20.515266+00:00
-- url     : https://prove2.me/theorems/6c1382f1-9f44-5b03-b259-08c8ad292d21
-- title:
--   crouzeix Polynomial Scalar Companion Regularized ball boundary eq: crouzeix Polynomial Scalar Companion Regularized ball boundary eq
-- statement:
--   On a centered circle, the cancelled transform evaluated at its boundary
--   point is exactly the difference between the conjugate center and boundary
--   values of the polynomial.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L75-L170
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L75-L170

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionRegularized_ball_boundary_eq
    {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ Metric.sphere (0 : ℂ) R) :
    crouzeixPolynomialScalarCompanionRegularized
        (SmoothJordanDomain.ball 0 R hR) p xi xi =
      star (Polynomial.eval 0 p) - star (Polynomial.eval xi p) := by sorry
