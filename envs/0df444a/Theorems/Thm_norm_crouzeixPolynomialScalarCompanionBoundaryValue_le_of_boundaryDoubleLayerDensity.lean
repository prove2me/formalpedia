-- Prove2me | Theorems.Thm_norm_crouzeixPolynomialScalarCompanionBoundaryValue_le_of_boundaryDoubleLayerDensity
-- name    : norm_crouzeixPolynomialScalarCompanionBoundaryValue_le_of_boundaryDoubleLayerDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:19:18.055625+00:00
-- url     : https://prove2.me/theorems/5a3e145c-373d-4143-9f43-0f1dc6225c41
-- title:
--   norm crouzeix Polynomial Scalar Companion Boundary Value le of boundary Double Layer Density: norm crouzeix Polynomial Scalar Companion Boundary Value le of boundary Double Layer Density
-- statement:
--   Integration of conjugate polynomial boundary data against a nonnegative
--   unit-mass double-layer density is contractive for the frontier sup norm.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasure.lean#L406-L476
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasure.lean#L406-L476

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
set_option autoImplicit false
open Complex MeasureTheory Polynomial Set
open scoped ComplexConjugate Interval Real

theorem norm_crouzeixPolynomialScalarCompanionBoundaryValue_le_of_boundaryDoubleLayerDensity
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ frontier Omega.carrier)
    (hrho : IntervalIntegrable
      (crouzeixBoundaryDoubleLayerDensity Omega xi)
      volume 0 (2 * Real.pi))
    (hmass : (∫ t in (0 : ℝ)..(2 * Real.pi),
      crouzeixBoundaryDoubleLayerDensity Omega xi t) = 1)
    (hpos : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      0 ≤ crouzeixBoundaryDoubleLayerDensity Omega xi t) :
    ‖crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) := by sorry
