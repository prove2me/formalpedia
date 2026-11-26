-- Prove2me | Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_add
-- name    : tendsto_crouzeixPolynomialScalarCompanionRegularized_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:41:05.090699+00:00
-- url     : https://prove2.me/theorems/9cf65271-f11d-483c-b27d-bfc44b4c795a
-- title:
--   tendsto crouzeix Polynomial Scalar Companion Regularized add: tendsto crouzeix Polynomial Scalar Companion Regularized add
-- statement:
--   Regularized Plemelj convergence is stable under polynomial addition.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L421-L444
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L421-L444

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem tendsto_crouzeixPolynomialScalarCompanionRegularized_add
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) (xi : ℂ)
    (hp : Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
    (hq : Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega q xi)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionRegularized Omega q xi xi))) :
    Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega (p + q) xi)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionRegularized
        Omega (p + q) xi xi)) := by sorry
