-- Prove2me | Theorems.Thm_integral_crouzeixBoundaryDoubleLayerDensity_complexAffine
-- name    : integral_crouzeixBoundaryDoubleLayerDensity_complexAffine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:33.184059+00:00
-- url     : https://prove2.me/theorems/178bfde7-d3c3-4046-9ce6-04078af88b72
-- title:
--   integral crouzeix Boundary Double Layer Density complex Affine: integral crouzeix Boundary Double Layer Density complex Affine
-- statement:
--   The total interval-integral mass of the double-layer density is invariant
--   under nonconstant complex-affine transport.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureAffine.lean#L178-L188
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureAffine.lean#L178-L188

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAffine
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped Interval Real

theorem integral_crouzeixBoundaryDoubleLayerDensity_complexAffine
    (Omega : SmoothJordanDomain) (a b xi : ℂ) (ha : a ≠ 0) :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      crouzeixBoundaryDoubleLayerDensity
        (Omega.complexAffine a b ha) (a * xi + b) t) =
      ∫ t in (0 : ℝ)..(2 * Real.pi),
        crouzeixBoundaryDoubleLayerDensity Omega xi t := by sorry
