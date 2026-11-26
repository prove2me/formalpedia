-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_eq_boundaryPhaseTransform
-- name    : crouzeixPolynomialScalarCompanionBoundaryValue_eq_boundaryPhaseTransform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:56:40.730744+00:00
-- url     : https://prove2.me/theorems/83e7ce03-e22f-4292-90ad-cad11892738f
-- title:
--   crouzeix Polynomial Scalar Companion Boundary Value eq boundary Phase Transform: crouzeix Polynomial Scalar Companion Boundary Value eq boundary Phase Transform
-- statement:
--   The explicit Plemelj boundary value is the conjugate point value plus
--   the lower-degree boundary phase transform.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L143-L152
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L143-L152

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionBoundaryValue_eq_boundaryPhaseTransform
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi =
      star (Polynomial.eval xi p) +
        crouzeixPolynomialBoundaryPhaseTransform Omega xi
          (p /ₘ (Polynomial.X - Polynomial.C xi)) := by sorry
