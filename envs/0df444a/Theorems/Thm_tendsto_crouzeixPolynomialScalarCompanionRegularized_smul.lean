-- Prove2me | Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_smul
-- name    : tendsto_crouzeixPolynomialScalarCompanionRegularized_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:40:22.178888+00:00
-- url     : https://prove2.me/theorems/72e8f1df-97cc-4c06-9212-d382da5d4fa1
-- title:
--   tendsto crouzeix Polynomial Scalar Companion Regularized smul: tendsto crouzeix Polynomial Scalar Companion Regularized smul
-- statement:
--   Regularized boundary convergence is preserved by polynomial scaling.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L118-L138
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L118-L138

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem tendsto_crouzeixPolynomialScalarCompanionRegularized_smul
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) (xi : ℂ)
    {l : Filter ℂ}
    (h : Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
      l
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi))) :
    Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega (a • p) xi)
      l
      (nhds (crouzeixPolynomialScalarCompanionRegularized
        Omega (a • p) xi xi)) := by sorry
