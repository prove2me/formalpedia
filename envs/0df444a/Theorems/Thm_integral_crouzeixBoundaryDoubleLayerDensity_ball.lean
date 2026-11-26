-- Prove2me | Theorems.Thm_integral_crouzeixBoundaryDoubleLayerDensity_ball
-- name    : integral_crouzeixBoundaryDoubleLayerDensity_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:24:35.287811+00:00
-- url     : https://prove2.me/theorems/99ba28f7-c1de-5579-8949-d5a6442bc229
-- title:
--   integral crouzeix Boundary Double Layer Density ball: integral crouzeix Boundary Double Layer Density ball
-- statement:
--   The boundary double-layer density of a positive circle has total mass
--   one at every boundary base point.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureCircle.lean#L83-L109
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureCircle.lean#L83-L109

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureCircle
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped ComplexConjugate Interval Real

theorem integral_crouzeixBoundaryDoubleLayerDensity_ball
    {c xi : ℂ} {R : ℝ} (hR : 0 < R)
    (hxi : xi ∈ Metric.sphere c R) :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      crouzeixBoundaryDoubleLayerDensity
        (SmoothJordanDomain.ball c R hR) xi t) = 1 := by sorry
