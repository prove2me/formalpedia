-- Prove2me | Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_sub_C_eval_iff
-- name    : tendsto_crouzeixPolynomialScalarCompanionRegularized_sub_C_eval_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:03:40.223016+00:00
-- url     : https://prove2.me/theorems/8329e6b5-a699-4504-8b11-3bba71d3c15e
-- title:
--   tendsto crouzeix Polynomial Scalar Companion Regularized sub C eval iff: tendsto crouzeix Polynomial Scalar Companion Regularized sub C eval iff
-- statement:
--   Regularized boundary convergence is equivalent for `p` and its
--   boundary-point normalization.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L158-L178
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L158-L178

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem tendsto_crouzeixPolynomialScalarCompanionRegularized_sub_C_eval_iff
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ)
    (l : Filter ℂ) :
    Tendsto
        (crouzeixPolynomialScalarCompanionRegularized Omega
          (p - Polynomial.C (Polynomial.eval xi p)) xi)
        l
        (nhds (crouzeixPolynomialScalarCompanionRegularized Omega
          (p - Polynomial.C (Polynomial.eval xi p)) xi xi)) ↔
      Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        l
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) := by sorry
