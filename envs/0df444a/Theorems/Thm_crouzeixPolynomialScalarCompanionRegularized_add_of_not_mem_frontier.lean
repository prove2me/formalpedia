-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_add_of_not_mem_frontier
-- name    : crouzeixPolynomialScalarCompanionRegularized_add_of_not_mem_frontier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:40:20.9703+00:00
-- url     : https://prove2.me/theorems/5f39e649-8a17-4518-a5f0-6a45591bb7f6
-- title:
--   crouzeix Polynomial Scalar Companion Regularized add of not mem frontier: crouzeix Polynomial Scalar Companion Regularized add of not mem frontier
-- statement:
--   Away from the frontier, the regularized transform is additive in its
--   polynomial argument.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L394-L418
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L394-L418

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionRegularized_add_of_not_mem_frontier
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) (xi : ℂ) {z : ℂ}
    (hz : z ∉ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanionRegularized Omega (p + q) xi z =
      crouzeixPolynomialScalarCompanionRegularized Omega p xi z +
        crouzeixPolynomialScalarCompanionRegularized Omega q xi z := by sorry
