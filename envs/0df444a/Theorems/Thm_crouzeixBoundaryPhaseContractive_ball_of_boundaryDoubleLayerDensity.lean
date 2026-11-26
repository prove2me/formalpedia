-- Prove2me | Theorems.Thm_crouzeixBoundaryPhaseContractive_ball_of_boundaryDoubleLayerDensity
-- name    : crouzeixBoundaryPhaseContractive_ball_of_boundaryDoubleLayerDensity
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:05:44.15692+00:00
-- url     : https://prove2.me/theorems/875a1ad0-5e0f-4b72-a365-fe849f7885e6
-- title:
--   crouzeix Boundary Phase Contractive ball of boundary Double Layer Density: crouzeix Boundary Phase Contractive ball of boundary Double Layer Density
-- statement:
--   Every polynomial satisfies the sharp boundary-phase invariant on a
--   positive-radius disk, obtained from the explicit circle probability
--   density.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureCircle.lean#L132-L150
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureCircle.lean#L132-L150

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureCircle
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped ComplexConjugate Interval Real

theorem crouzeixBoundaryPhaseContractive_ball_of_boundaryDoubleLayerDensity
    {c : ℂ} {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) :
    CrouzeixBoundaryPhaseContractive
      (SmoothJordanDomain.ball c R hR) p := by sorry
