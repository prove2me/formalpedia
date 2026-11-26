-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanion_eq_regularized_add
-- name    : crouzeixPolynomialScalarCompanion_eq_regularized_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:40:01.662481+00:00
-- url     : https://prove2.me/theorems/89b50bc8-0550-4350-8791-4917bf4f17c8
-- title:
--   crouzeix Polynomial Scalar Companion eq regularized add: crouzeix Polynomial Scalar Companion eq regularized add
-- statement:
--   Away from the frontier, the scalar companion is exactly the sum of its
--   regularized transform and the boundary datum times the normalized winding
--   kernel.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L481-L505
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L481-L505

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanion_eq_regularized_add
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) {z : ℂ}
    (hz : z ∉ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanion Omega p z =
      crouzeixPolynomialScalarCompanionRegularized Omega p xi z +
        star (Polynomial.eval xi p) * crouzeixScalarCauchyKernel Omega z := by sorry
