-- Prove2me | Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_le_of_isBounded_boundary
-- name    : norm_crouzeixPolynomialScalarCompanion_le_of_isBounded_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:16:14.59355+00:00
-- url     : https://prove2.me/theorems/ebe81efa-8e78-5ba6-a9f4-095c1692abe9
-- title:
--   norm crouzeix Polynomial Scalar Companion le of is Bounded boundary: norm crouzeix Polynomial Scalar Companion le of is Bounded boundary
-- statement:
--   A uniform bound for the explicit Plemelj boundary values controls the
--   scalar companion throughout every bounded normalized carrier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1753-L1771
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1753-L1771

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem norm_crouzeixPolynomialScalarCompanion_le_of_isBounded_boundary
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {C : ℝ}
    (hC : ∀ xi ∈ frontier Omega.carrier,
      ‖crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi‖ ≤ C)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤ C := by sorry
