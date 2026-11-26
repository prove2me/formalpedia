-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq_boundary_of_tendsto
-- name    : crouzeixPolynomialScalarCompanionClosedExtension_eq_boundary_of_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:36:23.471583+00:00
-- url     : https://prove2.me/theorems/13ebb76e-a21a-44f7-96b5-b3fe54d66bc8
-- title:
--   crouzeix Polynomial Scalar Companion Closed Extension eq boundary of tendsto: crouzeix Polynomial Scalar Companion Closed Extension eq boundary of tendsto
-- statement:
--   The canonical extension takes the prescribed Plemelj limit on the
--   frontier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundary.lean#L74-L81
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundary.lean#L74-L81

import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.ExtendFrom
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
set_option autoImplicit false
open Complex Filter Set

theorem crouzeixPolynomialScalarCompanionClosedExtension_eq_boundary_of_tendsto
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (b : ℂ → ℂ)
    (hlim : ∀ z ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanion Omega p)
        (nhdsWithin z Omega.carrier) (nhds (b z)))
    {z : ℂ} (hz : z ∈ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega p z = b z := by sorry
