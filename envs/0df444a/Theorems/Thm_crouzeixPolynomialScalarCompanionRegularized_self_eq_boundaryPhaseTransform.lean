-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_self_eq_boundaryPhaseTransform
-- name    : crouzeixPolynomialScalarCompanionRegularized_self_eq_boundaryPhaseTransform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:56:29.81151+00:00
-- url     : https://prove2.me/theorems/475fa567-b7ec-4215-914e-6db978f3834a
-- title:
--   crouzeix Polynomial Scalar Companion Regularized self eq boundary Phase Transform: crouzeix Polynomial Scalar Companion Regularized self eq boundary Phase Transform
-- statement:
--   The regularized self-value is the named boundary phase transform of the
--   divided difference.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L130-L139
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L130-L139

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionRegularized_self_eq_boundaryPhaseTransform
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionRegularized Omega p xi xi =
      crouzeixPolynomialBoundaryPhaseTransform Omega xi
        (p /ₘ (Polynomial.X - Polynomial.C xi)) := by sorry
