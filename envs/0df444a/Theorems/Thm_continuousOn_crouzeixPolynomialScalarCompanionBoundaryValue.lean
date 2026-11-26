-- Prove2me | Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionBoundaryValue
-- name    : continuousOn_crouzeixPolynomialScalarCompanionBoundaryValue
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:44:49.080879+00:00
-- url     : https://prove2.me/theorems/1cc1d924-d32b-5d12-b4d3-27deccd7a142
-- title:
--   continuous On crouzeix Polynomial Scalar Companion Boundary Value: continuous On crouzeix Polynomial Scalar Companion Boundary Value
-- statement:
--   The explicit Plemelj boundary value is continuous on the frontier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1260-L1269
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1260-L1269

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem continuousOn_crouzeixPolynomialScalarCompanionBoundaryValue
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    ContinuousOn
      (crouzeixPolynomialScalarCompanionBoundaryValue Omega p)
      (frontier Omega.carrier) := by sorry
