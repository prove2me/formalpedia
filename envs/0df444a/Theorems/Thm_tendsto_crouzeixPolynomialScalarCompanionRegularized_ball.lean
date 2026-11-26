-- Prove2me | Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_ball
-- name    : tendsto_crouzeixPolynomialScalarCompanionRegularized_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:17:03.560786+00:00
-- url     : https://prove2.me/theorems/58d8666b-ca78-4f4d-bd0d-50775f354648
-- title:
--   tendsto crouzeix Polynomial Scalar Companion Regularized ball: tendsto crouzeix Polynomial Scalar Companion Regularized ball
-- statement:
--   On a centered disk, the regularized transform converges at every
--   frontier point to its explicitly evaluated boundary integral.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L174-L207
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L174-L207

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real

theorem tendsto_crouzeixPolynomialScalarCompanionRegularized_ball
    {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ Metric.sphere (0 : ℂ) R) :
    Tendsto
      (crouzeixPolynomialScalarCompanionRegularized
        (SmoothJordanDomain.ball 0 R hR) p xi)
      (nhdsWithin xi (Metric.ball (0 : ℂ) R))
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized
          (SmoothJordanDomain.ball 0 R hR) p xi xi)) := by sorry
