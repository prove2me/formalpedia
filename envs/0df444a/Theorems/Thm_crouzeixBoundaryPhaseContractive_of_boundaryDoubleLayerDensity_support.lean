-- Prove2me | Theorems.Thm_crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity_support
-- name    : crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:17:58.51156+00:00
-- url     : https://prove2.me/theorems/7f1f46bb-26f7-5c01-bcf4-abf0b1dc337d
-- title:
--   crouzeix Boundary Phase Contractive of boundary Double Layer Density support: crouzeix Boundary Phase Contractive of boundary Double Layer Density support
-- statement:
--   The sharp boundary-phase invariant follows directly from integrability,
--   unit mass, and the oriented supporting-normal inequality on the frontier.
--   The pointwise density sign is discharged algebraically.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasure.lean#L502-L520
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasure.lean#L502-L520

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
set_option autoImplicit false
open Complex MeasureTheory Polynomial Set
open scoped ComplexConjugate Interval Real

theorem crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity_support
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hrho : ∀ xi ∈ frontier Omega.carrier,
      IntervalIntegrable (crouzeixBoundaryDoubleLayerDensity Omega xi)
        volume 0 (2 * Real.pi))
    (hmass : ∀ xi ∈ frontier Omega.carrier,
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        crouzeixBoundaryDoubleLayerDensity Omega xi t) = 1)
    (hsupport : ∀ xi ∈ frontier Omega.carrier,
      ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
        ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
          (xi - Omega.boundaryParam t)).re ≤ 0) :
    CrouzeixBoundaryPhaseContractive Omega p := by sorry
