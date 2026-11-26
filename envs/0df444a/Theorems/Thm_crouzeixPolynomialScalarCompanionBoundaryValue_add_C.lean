-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_add_C
-- name    : crouzeixPolynomialScalarCompanionBoundaryValue_add_C
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:03:49.870155+00:00
-- url     : https://prove2.me/theorems/765ac028-4ffe-501e-b083-495c13c45ec3
-- title:
--   crouzeix Polynomial Scalar Companion Boundary Value add C: crouzeix Polynomial Scalar Companion Boundary Value add C
-- statement:
--   The explicit Plemelj boundary value is conjugate-affine under addition
--   of a constant polynomial.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L195-L203
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L195-L203

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionBoundaryValue_add_C
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (a xi : ℂ) :
    crouzeixPolynomialScalarCompanionBoundaryValue Omega
        (p + Polynomial.C a) xi =
      star a + crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi := by sorry
