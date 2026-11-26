-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_smul
-- name    : crouzeixPolynomialScalarCompanionBoundaryValue_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:39:55.956515+00:00
-- url     : https://prove2.me/theorems/cebe8e4c-6a00-5b49-9fd0-1400957c96bd
-- title:
--   crouzeix Polynomial Scalar Companion Boundary Value smul: crouzeix Polynomial Scalar Companion Boundary Value smul
-- statement:
--   The explicit Plemelj boundary value is conjugate-homogeneous in the
--   polynomial argument.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L207-L221
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L207-L221

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionBoundaryValue_smul
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionBoundaryValue Omega (a • p) xi =
      star a *
        crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi := by sorry
