-- Prove2me | Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_le_of_boundary_of_cauchyKernel_eq_one
-- name    : norm_crouzeixPolynomialScalarCompanion_le_of_boundary_of_cauchyKernel_eq_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:45:14.660099+00:00
-- url     : https://prove2.me/theorems/e938af13-3901-5b9a-81b8-9f3374bc30b0
-- title:
--   norm crouzeix Polynomial Scalar Companion le of boundary of cauchy Kernel eq one: norm crouzeix Polynomial Scalar Companion le of boundary of cauchy Kernel eq one
-- statement:
--   Under winding normalization alone, a uniform Plemelj boundary bound
--   controls the scalar companion throughout the carrier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1806-L1819
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1806-L1819

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem norm_crouzeixPolynomialScalarCompanion_le_of_boundary_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {C : ℝ}
    (hC : ∀ xi ∈ frontier Omega.carrier,
      ‖crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi‖ ≤ C)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤ C := by sorry
