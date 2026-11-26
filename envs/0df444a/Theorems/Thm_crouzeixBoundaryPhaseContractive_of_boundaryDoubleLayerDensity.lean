-- Prove2me | Theorems.Thm_crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity
-- name    : crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:16:56.824189+00:00
-- url     : https://prove2.me/theorems/33030696-11cb-523f-8abb-a1853f63f5d4
-- title:
--   crouzeix Boundary Phase Contractive of boundary Double Layer Density: crouzeix Boundary Phase Contractive of boundary Double Layer Density
-- statement:
--   Nonnegativity and unit mass of the explicit boundary double-layer
--   density imply the sharp boundary-phase invariant.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasure.lean#L480-L497
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasure.lean#L480-L497

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
set_option autoImplicit false
open Complex MeasureTheory Polynomial Set
open scoped ComplexConjugate Interval Real

theorem crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hrho : ∀ xi ∈ frontier Omega.carrier,
      IntervalIntegrable (crouzeixBoundaryDoubleLayerDensity Omega xi)
        volume 0 (2 * Real.pi))
    (hmass : ∀ xi ∈ frontier Omega.carrier,
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        crouzeixBoundaryDoubleLayerDensity Omega xi t) = 1)
    (hpos : ∀ xi ∈ frontier Omega.carrier,
      ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
        0 ≤ crouzeixBoundaryDoubleLayerDensity Omega xi t) :
    CrouzeixBoundaryPhaseContractive Omega p := by sorry
