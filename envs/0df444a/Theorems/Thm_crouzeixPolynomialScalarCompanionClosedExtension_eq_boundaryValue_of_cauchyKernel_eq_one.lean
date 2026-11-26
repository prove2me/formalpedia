-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_cauchyKernel_eq_one
-- name    : crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_cauchyKernel_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:45:05.734906+00:00
-- url     : https://prove2.me/theorems/57ad6e89-8592-590b-88e9-f4e212a517f8
-- title:
--   crouzeix Polynomial Scalar Companion Closed Extension eq boundary Value of cauchy Kernel eq one: crouzeix Polynomial Scalar Companion Closed Extension eq boundary Value of cauchy Kernel eq one
-- statement:
--   Under winding normalization alone, the canonical closed extension takes
--   the explicit Plemelj value on the frontier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1650-L1665
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1650-L1665

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {xi : ℂ} (hxi : xi ∈ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega p xi =
      crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi := by sorry
