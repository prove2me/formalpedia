-- Prove2me | Theorems.Thm_crouzeixBoundaryPhaseContractive_of_oriented_carrier_point
-- name    : crouzeixBoundaryPhaseContractive_of_oriented_carrier_point
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:48:44.261062+00:00
-- url     : https://prove2.me/theorems/0e0b2799-fe8e-5ed5-88f8-120e9d0209d0
-- title:
--   crouzeix Boundary Phase Contractive of oriented carrier point: crouzeix Boundary Phase Contractive of oriented carrier point
-- statement:
--   A consistently oriented point of the carrier makes every polynomial
--   boundary phase contractive.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureMass.lean#L453-L470
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureMass.lean#L453-L470

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixBoundaryPhaseContractive_of_oriented_carrier_point
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0)
    (p : Polynomial ℂ) :
    CrouzeixBoundaryPhaseContractive Omega p := by sorry
