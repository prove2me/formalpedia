-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_sub_C_eval
-- name    : crouzeixPolynomialScalarCompanionRegularized_sub_C_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:39:45.131387+00:00
-- url     : https://prove2.me/theorems/a425eee5-de25-4b0a-b6b9-1c9361cbf22d
-- title:
--   crouzeix Polynomial Scalar Companion Regularized sub C eval: crouzeix Polynomial Scalar Companion Regularized sub C eval
-- statement:
--   Regularization is unchanged after replacing `p` by the canonical
--   polynomial `p - C (p.eval xi)` that vanishes at `xi`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L147-L154
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L147-L154

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionRegularized_sub_C_eval
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi z : ℂ) :
    crouzeixPolynomialScalarCompanionRegularized Omega
        (p - Polynomial.C (Polynomial.eval xi p)) xi z =
      crouzeixPolynomialScalarCompanionRegularized Omega p xi z := by sorry
