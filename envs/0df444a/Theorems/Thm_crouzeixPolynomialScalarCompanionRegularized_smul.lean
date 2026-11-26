-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_smul
-- name    : crouzeixPolynomialScalarCompanionRegularized_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:39:50.888789+00:00
-- url     : https://prove2.me/theorems/0ef56a54-c2d8-4ec3-b36d-c30c1513cf4c
-- title:
--   crouzeix Polynomial Scalar Companion Regularized smul: crouzeix Polynomial Scalar Companion Regularized smul
-- statement:
--   The cancelled regularized transform is conjugate-homogeneous in the
--   polynomial argument.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L88-L107
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L88-L107

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionRegularized_smul
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) (xi z : ℂ) :
    crouzeixPolynomialScalarCompanionRegularized Omega (a • p) xi z =
      star a *
        crouzeixPolynomialScalarCompanionRegularized Omega p xi z := by sorry
