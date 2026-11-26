-- Prove2me | Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionRegularized_self
-- name    : continuousOn_crouzeixPolynomialScalarCompanionRegularized_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:07:16.948693+00:00
-- url     : https://prove2.me/theorems/cf8ec0db-d91a-5488-84af-fe1788a12916
-- title:
--   continuous On crouzeix Polynomial Scalar Companion Regularized self: continuous On crouzeix Polynomial Scalar Companion Regularized self
-- statement:
--   The regularized self-value varies continuously along the frontier.  The
--   moving removable singularity is handled by dominated convergence, using
--   joint continuity and the compact-uniform bound for divided differences.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1145-L1257
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1145-L1257

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem continuousOn_crouzeixPolynomialScalarCompanionRegularized_self
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    ContinuousOn
      (fun xi =>
        crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)
      (frontier Omega.carrier) := by sorry
