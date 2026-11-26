-- Prove2me | Theorems.Thm_intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_of_integral_eq_one
-- name    : intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_of_integral_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:16:52.31911+00:00
-- url     : https://prove2.me/theorems/2aefb3cc-e847-5414-83c4-6dac6823d1ab
-- title:
--   interval Integrable crouzeix Boundary Double Layer Density of integral eq one: interval Integrable crouzeix Boundary Double Layer Density of integral eq one
-- statement:
--   Unit interval-integral mass forces integrability.  This uses the Bochner
--   integral convention that a nonintegrable function has integral zero, so the
--   nonzero mass hypothesis already contains the required integrability datum.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasure.lean#L47-L60
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasure.lean#L47-L60

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
set_option autoImplicit false
open Complex MeasureTheory Polynomial Set
open scoped ComplexConjugate Interval Real

theorem intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_of_integral_eq_one
    (Omega : SmoothJordanDomain) (xi : ℂ)
    (hmass : (∫ t in (0 : ℝ)..(2 * Real.pi),
      crouzeixBoundaryDoubleLayerDensity Omega xi t) = 1) :
    IntervalIntegrable (crouzeixBoundaryDoubleLayerDensity Omega xi)
      volume 0 (2 * Real.pi) := by sorry
