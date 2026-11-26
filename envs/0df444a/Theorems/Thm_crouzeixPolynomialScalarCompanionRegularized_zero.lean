-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
-- name    : crouzeixPolynomialScalarCompanionRegularized_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:39:12.498491+00:00
-- url     : https://prove2.me/theorems/649151f4-23bb-4218-98e7-0a079af92a5f
-- title:
--   crouzeix Polynomial Scalar Companion Regularized zero: crouzeix Polynomial Scalar Companion Regularized zero
-- statement:
--   The regularized transform of the zero polynomial vanishes.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L110-L115
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L110-L115

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionRegularized_zero
    (Omega : SmoothJordanDomain) (xi z : ℂ) :
    crouzeixPolynomialScalarCompanionRegularized Omega 0 xi z = 0 := by sorry
