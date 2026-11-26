-- Prove2me | Theorems.Thm_crouzeixBoundaryDoubleLayerDensity_complexAffine
-- name    : crouzeixBoundaryDoubleLayerDensity_complexAffine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:16.462587+00:00
-- url     : https://prove2.me/theorems/787c5e85-ae05-425c-a6b1-3f3f7ba70b00
-- title:
--   crouzeix Boundary Double Layer Density complex Affine: crouzeix Boundary Double Layer Density complex Affine
-- statement:
--   Simultaneously transporting the domain and base point by a nonconstant
--   complex-affine map leaves the scalar double-layer density unchanged.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureAffine.lean#L122-L157
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureAffine.lean#L122-L157

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAffine
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped Interval Real

theorem crouzeixBoundaryDoubleLayerDensity_complexAffine
    (Omega : SmoothJordanDomain) (a b xi : ℂ) (ha : a ≠ 0) (t : ℝ) :
    crouzeixBoundaryDoubleLayerDensity (Omega.complexAffine a b ha)
        (a * xi + b) t =
      crouzeixBoundaryDoubleLayerDensity Omega xi t := by sorry
