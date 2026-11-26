-- Prove2me | Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_le_of_regularized_boundary
-- name    : norm_crouzeixPolynomialScalarCompanion_le_of_regularized_boundary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:55:21.707945+00:00
-- url     : https://prove2.me/theorems/e44bcf9a-9dc8-474d-9cc0-698a836890e8
-- title:
--   norm crouzeix Polynomial Scalar Companion le of regularized boundary: norm crouzeix Polynomial Scalar Companion le of regularized boundary
-- statement:
--   If the explicit regularized Plemelj values have norm at most `C` on the
--   frontier, the scalar companion has the same bound throughout the carrier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L702-L721
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L702-L721

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem norm_crouzeixPolynomialScalarCompanion_le_of_regularized_boundary
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1)
    (hreg : ∀ xi ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
    {C : ℝ}
    (hC : ∀ xi ∈ frontier Omega.carrier,
      ‖crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi‖ ≤ C)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤ C := by sorry
