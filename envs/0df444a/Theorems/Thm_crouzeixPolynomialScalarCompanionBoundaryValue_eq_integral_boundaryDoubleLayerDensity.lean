-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_eq_integral_boundaryDoubleLayerDensity
-- name    : crouzeixPolynomialScalarCompanionBoundaryValue_eq_integral_boundaryDoubleLayerDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:36.821769+00:00
-- url     : https://prove2.me/theorems/0178d045-78e1-45ba-8929-69112d1272b8
-- title:
--   crouzeix Polynomial Scalar Companion Boundary Value eq integral boundary Double Layer Density: crouzeix Polynomial Scalar Companion Boundary Value eq integral boundary Double Layer Density
-- statement:
--   The Plemelj boundary value is the conjugate polynomial boundary datum
--   integrated against the scalar double-layer density, provided that density is
--   integrable and has unit mass.  The analytic half of the kernel cancels as a
--   closed polynomial contour.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasure.lean#L197-L402
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasure.lean#L197-L402

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
set_option autoImplicit false
open Complex MeasureTheory Polynomial Set
open scoped ComplexConjugate Interval Real

theorem crouzeixPolynomialScalarCompanionBoundaryValue_eq_integral_boundaryDoubleLayerDensity
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ frontier Omega.carrier)
    (hrho : IntervalIntegrable
      (crouzeixBoundaryDoubleLayerDensity Omega xi)
      volume 0 (2 * Real.pi))
    (hmass : (∫ t in (0 : ℝ)..(2 * Real.pi),
      crouzeixBoundaryDoubleLayerDensity Omega xi t) = 1) :
    crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi =
      ∫ t in (0 : ℝ)..(2 * Real.pi),
        (crouzeixBoundaryDoubleLayerDensity Omega xi t : ℂ) *
          star (Polynomial.eval (Omega.boundaryParam t) p) := by sorry
