-- Prove2me | Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_ball_center
-- name    : tendsto_crouzeixPolynomialScalarCompanionRegularized_ball_center
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:15:11.844828+00:00
-- url     : https://prove2.me/theorems/98004c84-4bb3-43e7-a8f8-f02ef612cec9
-- title:
--   tendsto crouzeix Polynomial Scalar Companion Regularized ball center: tendsto crouzeix Polynomial Scalar Companion Regularized ball center
-- statement:
--   The regularized transform converges at every boundary point of an
--   arbitrarily centered disk.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L423-L456
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L423-L456

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real

theorem tendsto_crouzeixPolynomialScalarCompanionRegularized_ball_center
    (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ Metric.sphere c R) :
    Tendsto
      (crouzeixPolynomialScalarCompanionRegularized
        (SmoothJordanDomain.ball c R hR) p xi)
      (nhdsWithin xi (Metric.ball c R))
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized
          (SmoothJordanDomain.ball c R hR) p xi xi)) := by sorry
