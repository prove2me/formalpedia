-- Prove2me | Theorems.Thm_crouzeixBoundaryDoubleLayerDensity_periodic
-- name    : crouzeixBoundaryDoubleLayerDensity_periodic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:19:31.384985+00:00
-- url     : https://prove2.me/theorems/deba9abd-75ce-4b59-abaa-b41101bfad1b
-- title:
--   crouzeix Boundary Double Layer Density periodic: crouzeix Boundary Double Layer Density periodic
-- statement:
--   The explicit boundary double-layer density has the same period as the
--   boundary trace.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureMass.lean#L48-L55
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureMass.lean#L48-L55

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixBoundaryDoubleLayerDensity_periodic
    (Omega : SmoothJordanDomain) (xi : ℂ) :
    Function.Periodic
      (crouzeixBoundaryDoubleLayerDensity Omega xi) (2 * Real.pi) := by sorry
