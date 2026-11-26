-- Prove2me | Theorems.Thm_crouzeixScalarCauchyKernel_ball_center_eq_one
-- name    : crouzeixScalarCauchyKernel_ball_center_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:14:18.469269+00:00
-- url     : https://prove2.me/theorems/c4ed38d8-ed6a-564d-b540-9b6f2acc3a03
-- title:
--   crouzeix Scalar Cauchy Kernel ball center eq one: crouzeix Scalar Cauchy Kernel ball center eq one
-- statement:
--   The normalized scalar Cauchy kernel is one throughout the interior of an
--   arbitrarily centered positively oriented circle.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L281-L288
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljCircle.lean#L281-L288

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real

theorem crouzeixScalarCauchyKernel_ball_center_eq_one
    (c : ℂ) {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ Metric.ball c R) :
    crouzeixScalarCauchyKernel (SmoothJordanDomain.ball c R hR) z = 1 := by sorry
