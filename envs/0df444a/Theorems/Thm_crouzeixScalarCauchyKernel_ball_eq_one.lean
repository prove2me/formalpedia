-- Prove2me | Theorems.Thm_crouzeixScalarCauchyKernel_ball_eq_one
-- name    : crouzeixScalarCauchyKernel_ball_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:14:10.230585+00:00
-- url     : https://prove2.me/theorems/20429245-db2e-52b3-81cf-38b6fc8c3163
-- title:
--   crouzeix Scalar Cauchy Kernel ball eq one: crouzeix Scalar Cauchy Kernel ball eq one
-- statement:
--   The normalized scalar Cauchy kernel of a positively oriented centered
--   circle is one throughout its interior.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L46-L52
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L46-L52

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real

theorem crouzeixScalarCauchyKernel_ball_eq_one
    {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    crouzeixScalarCauchyKernel (SmoothJordanDomain.ball 0 R hR) z = 1 := by sorry
