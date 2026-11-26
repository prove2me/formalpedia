-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_isBounded
-- name    : crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_isBounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:16:13.915329+00:00
-- url     : https://prove2.me/theorems/80bb38f8-0c8d-5aa3-81f5-7adeace6a8cf
-- title:
--   crouzeix Polynomial Scalar Companion Closed Extension eq boundary Value of is Bounded: crouzeix Polynomial Scalar Companion Closed Extension eq boundary Value of is Bounded
-- statement:
--   On a bounded smooth Jordan carrier, the canonical closed extension takes
--   the explicit Plemelj boundary value at every frontier point.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1688-L1704
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1688-L1704

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_isBounded
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {xi : ℂ} (hxi : xi ∈ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega p xi =
      crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi := by sorry
