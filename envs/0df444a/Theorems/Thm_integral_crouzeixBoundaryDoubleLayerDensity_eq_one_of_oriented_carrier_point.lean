-- Prove2me | Theorems.Thm_integral_crouzeixBoundaryDoubleLayerDensity_eq_one_of_oriented_carrier_point
-- name    : integral_crouzeixBoundaryDoubleLayerDensity_eq_one_of_oriented_carrier_point
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:18:04.146175+00:00
-- url     : https://prove2.me/theorems/78dbee41-6ec4-5351-af8f-1309ef32368e
-- title:
--   integral crouzeix Boundary Double Layer Density eq one of oriented carrier point: integral crouzeix Boundary Double Layer Density eq one of oriented carrier point
-- statement:
--   If one point of the open carrier lies consistently on the inward side of
--   the canonical oriented tangent line, then the boundary double-layer density
--   based at every frontier point has interval-integral mass one.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureMass.lean#L108-L449
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureMass.lean#L108-L449

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem integral_crouzeixBoundaryDoubleLayerDensity_eq_one_of_oriented_carrier_point
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0)
    (xi : ℂ) (hxi : xi ∈ frontier Omega.carrier) :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      crouzeixBoundaryDoubleLayerDensity Omega xi t) = 1 := by sorry
