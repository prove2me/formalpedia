-- Prove2me | Theorems.Thm_crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity_mass_support
-- name    : crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity_mass_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:19:19.064394+00:00
-- url     : https://prove2.me/theorems/b1284c22-16da-4ff0-acab-5c537fe5f7e7
-- title:
--   crouzeix Boundary Phase Contractive of boundary Double Layer Density mass support: crouzeix Boundary Phase Contractive of boundary Double Layer Density mass support
-- statement:
--   Unit mass and oriented frontier support alone imply the sharp
--   boundary-phase invariant.  A separate integrability assumption is redundant:
--   mass one rules out the nonintegrable zero-integral convention.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasure.lean#L525-L544
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasure.lean#L525-L544

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
set_option autoImplicit false
open Complex MeasureTheory Polynomial Set
open scoped ComplexConjugate Interval Real

theorem crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity_mass_support
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hmass : ∀ xi ∈ frontier Omega.carrier,
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        crouzeixBoundaryDoubleLayerDensity Omega xi t) = 1)
    (hsupport : ∀ xi ∈ frontier Omega.carrier,
      ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
        ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
          (xi - Omega.boundaryParam t)).re ≤ 0) :
    CrouzeixBoundaryPhaseContractive Omega p := by sorry
