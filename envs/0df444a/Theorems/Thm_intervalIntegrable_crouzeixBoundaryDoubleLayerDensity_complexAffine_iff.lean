-- Prove2me | Theorems.Thm_intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_complexAffine_iff
-- name    : intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_complexAffine_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:46:30.98035+00:00
-- url     : https://prove2.me/theorems/81c904b6-aa55-4121-9fa1-67b660d53ddb
-- title:
--   interval Integrable crouzeix Boundary Double Layer Density complex Affine iff: interval Integrable crouzeix Boundary Double Layer Density complex Affine iff
-- statement:
--   Interval integrability of the transported density is equivalent to that
--   of the original density.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureAffine.lean#L161-L174
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureAffine.lean#L161-L174

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAffine
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped Interval Real

theorem intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_complexAffine_iff
    (Omega : SmoothJordanDomain) (a b xi : ℂ) (ha : a ≠ 0) :
    IntervalIntegrable
        (crouzeixBoundaryDoubleLayerDensity
          (Omega.complexAffine a b ha) (a * xi + b))
        volume 0 (2 * Real.pi) ↔
      IntervalIntegrable (crouzeixBoundaryDoubleLayerDensity Omega xi)
        volume 0 (2 * Real.pi) := by sorry
