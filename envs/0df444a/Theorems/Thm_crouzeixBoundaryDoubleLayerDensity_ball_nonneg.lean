-- Prove2me | Theorems.Thm_crouzeixBoundaryDoubleLayerDensity_ball_nonneg
-- name    : crouzeixBoundaryDoubleLayerDensity_ball_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:24:38.689807+00:00
-- url     : https://prove2.me/theorems/a4bd58ce-7f52-5b42-8459-5c758f976ad6
-- title:
--   crouzeix Boundary Double Layer Density ball nonneg: crouzeix Boundary Double Layer Density ball nonneg
-- statement:
--   The boundary double-layer density of a positive circle is everywhere
--   nonnegative, including its inverse-at-zero value at the base point.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureCircle.lean#L113-L127
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureCircle.lean#L113-L127

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureCircle
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped ComplexConjugate Interval Real

theorem crouzeixBoundaryDoubleLayerDensity_ball_nonneg
    {c xi : ℂ} {R : ℝ} (hR : 0 < R)
    (hxi : xi ∈ Metric.sphere c R) (t : ℝ) :
    0 ≤ crouzeixBoundaryDoubleLayerDensity
      (SmoothJordanDomain.ball c R hR) xi t := by sorry
