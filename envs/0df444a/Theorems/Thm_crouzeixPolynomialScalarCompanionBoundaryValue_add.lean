-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_add
-- name    : crouzeixPolynomialScalarCompanionBoundaryValue_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:41:10.869334+00:00
-- url     : https://prove2.me/theorems/11ef92ff-cafb-5e3d-b450-1c816e0f9c02
-- title:
--   crouzeix Polynomial Scalar Companion Boundary Value add: crouzeix Polynomial Scalar Companion Boundary Value add
-- statement:
--   The explicit Plemelj boundary value is additive in the polynomial
--   argument.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L448-L456
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L448-L456

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionBoundaryValue_add
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionBoundaryValue Omega (p + q) xi =
      crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi +
        crouzeixPolynomialScalarCompanionBoundaryValue Omega q xi := by sorry
