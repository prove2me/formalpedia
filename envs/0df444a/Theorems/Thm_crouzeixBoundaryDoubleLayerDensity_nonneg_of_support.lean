-- Prove2me | Theorems.Thm_crouzeixBoundaryDoubleLayerDensity_nonneg_of_support
-- name    : crouzeixBoundaryDoubleLayerDensity_nonneg_of_support
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:10:00.918136+00:00
-- url     : https://prove2.me/theorems/adfd6fd1-9f7a-4b10-915f-1539fec5ba88
-- title:
--   crouzeix Boundary Double Layer Density nonneg of support: crouzeix Boundary Double Layer Density nonneg of support
-- statement:
--   An oriented supporting-normal inequality at the boundary trace makes the
--   scalar double-layer density nonnegative.  This records the exact orientation
--   data absent from the bare `SmoothJordanDomain` structure.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasure.lean#L65-L89
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasure.lean#L65-L89

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
set_option autoImplicit false
open Complex MeasureTheory Polynomial Set
open scoped ComplexConjugate Interval Real

theorem crouzeixBoundaryDoubleLayerDensity_nonneg_of_support
    (Omega : SmoothJordanDomain) (xi : ℂ) (t : ℝ)
    (hsupport :
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (xi - Omega.boundaryParam t)).re ≤ 0) :
    0 ≤ crouzeixBoundaryDoubleLayerDensity Omega xi t := by sorry
