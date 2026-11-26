-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_eq_add_normalized
-- name    : crouzeixPolynomialScalarCompanionBoundaryValue_eq_add_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:03:47.1112+00:00
-- url     : https://prove2.me/theorems/470c51ff-b9fb-4c40-abba-f69b777d9791
-- title:
--   crouzeix Polynomial Scalar Companion Boundary Value eq add normalized: crouzeix Polynomial Scalar Companion Boundary Value eq add normalized
-- statement:
--   The Plemelj value splits into the conjugate boundary datum plus the
--   boundary value of the polynomial normalized to vanish at `xi`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L182-L191
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L182-L191

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionBoundaryValue_eq_add_normalized
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi =
      star (Polynomial.eval xi p) +
        crouzeixPolynomialScalarCompanionBoundaryValue Omega
          (p - Polynomial.C (Polynomial.eval xi p)) xi := by sorry
