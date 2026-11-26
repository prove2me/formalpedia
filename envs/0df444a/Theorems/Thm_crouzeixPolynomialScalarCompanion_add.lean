-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanion_add
-- name    : crouzeixPolynomialScalarCompanion_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:41:12.361225+00:00
-- url     : https://prove2.me/theorems/86ce9833-a1b5-468c-9f54-749ed3494a07
-- title:
--   crouzeix Polynomial Scalar Companion add: crouzeix Polynomial Scalar Companion add
-- statement:
--   Away from the frontier, the full scalar companion is additive in its
--   polynomial argument.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L509-L523
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L509-L523

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanion_add
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) {z : ℂ}
    (hz : z ∉ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanion Omega (p + q) z =
      crouzeixPolynomialScalarCompanion Omega p z +
        crouzeixPolynomialScalarCompanion Omega q z := by sorry
