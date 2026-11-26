-- Prove2me | Theorems.Thm_crouzeixBoundaryPhaseContractive_complexAffine_of_boundaryDoubleLayerProbability
-- name    : crouzeixBoundaryPhaseContractive_complexAffine_of_boundaryDoubleLayerProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:04:56.498811+00:00
-- url     : https://prove2.me/theorems/c5805793-707f-4daf-83a5-e564e84de776
-- title:
--   crouzeix Boundary Phase Contractive complex Affine of boundary Double Layer Probability: crouzeix Boundary Phase Contractive complex Affine of boundary Double Layer Probability
-- statement:
--   If the original frontier carries a pointwise nonnegative unit-mass
--   double-layer density, then every polynomial satisfies the sharp boundary
--   phase estimate on every nonconstant complex-affine image of the domain.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureAffine.lean#L193-L223
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureAffine.lean#L193-L223

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAffine
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped Interval Real

theorem crouzeixBoundaryPhaseContractive_complexAffine_of_boundaryDoubleLayerProbability
    (Omega : SmoothJordanDomain) (a b : ℂ) (ha : a ≠ 0)
    (p : Polynomial ℂ)
    (hmass : ∀ xi ∈ frontier Omega.carrier,
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        crouzeixBoundaryDoubleLayerDensity Omega xi t) = 1)
    (hpos : ∀ xi ∈ frontier Omega.carrier,
      ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
        0 ≤ crouzeixBoundaryDoubleLayerDensity Omega xi t) :
    CrouzeixBoundaryPhaseContractive (Omega.complexAffine a b ha) p := by sorry
