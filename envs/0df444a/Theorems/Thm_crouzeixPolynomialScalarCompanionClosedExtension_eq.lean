-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq
-- name    : crouzeixPolynomialScalarCompanionClosedExtension_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:36:19.660921+00:00
-- url     : https://prove2.me/theorems/80ac95c5-361f-42a6-9ea5-05fa30d190c1
-- title:
--   crouzeix Polynomial Scalar Companion Closed Extension eq: crouzeix Polynomial Scalar Companion Closed Extension eq
-- statement:
--   The canonical limit extension agrees with the scalar companion at every
--   interior point, independently of any boundary-value theorem.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundary.lean#L45-L51
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundary.lean#L45-L51

import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.ExtendFrom
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
set_option autoImplicit false
open Complex Filter Set

theorem crouzeixPolynomialScalarCompanionClosedExtension_eq
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega p z =
      crouzeixPolynomialScalarCompanion Omega p z := by sorry
