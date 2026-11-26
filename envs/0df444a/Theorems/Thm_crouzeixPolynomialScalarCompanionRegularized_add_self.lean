-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_add_self
-- name    : crouzeixPolynomialScalarCompanionRegularized_add_self
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:40:33.363023+00:00
-- url     : https://prove2.me/theorems/13edb2fe-c9cb-439d-acf4-2d02e8f994fd
-- title:
--   crouzeix Polynomial Scalar Companion Regularized add self: crouzeix Polynomial Scalar Companion Regularized add self
-- statement:
--   At the cancelled base point, the regularized transform is additive in
--   the polynomial argument.  The integrability needed for interval-integral
--   additivity is supplied by the preceding cancellation theorem.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L365-L390
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L365-L390

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionRegularized_add_self
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionRegularized Omega (p + q) xi xi =
      crouzeixPolynomialScalarCompanionRegularized Omega p xi xi +
        crouzeixPolynomialScalarCompanionRegularized Omega q xi xi := by sorry
