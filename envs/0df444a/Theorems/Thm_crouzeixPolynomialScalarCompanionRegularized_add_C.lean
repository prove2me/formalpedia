-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_add_C
-- name    : crouzeixPolynomialScalarCompanionRegularized_add_C
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:39:29.655948+00:00
-- url     : https://prove2.me/theorems/4a223800-fa83-5771-ba40-2329e6104ed0
-- title:
--   crouzeix Polynomial Scalar Companion Regularized add C: crouzeix Polynomial Scalar Companion Regularized add C
-- statement:
--   Adding a constant polynomial does not change the cancelled regularized
--   transform.  Thus all singular boundary analysis may be normalized by
--   subtracting the polynomial value at the selected boundary point.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L73-L84
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L73-L84

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionRegularized_add_C
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (a xi z : ℂ) :
    crouzeixPolynomialScalarCompanionRegularized Omega
        (p + Polynomial.C a) xi z =
      crouzeixPolynomialScalarCompanionRegularized Omega p xi z := by sorry
