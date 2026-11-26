-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
-- name    : crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:40:18.74459+00:00
-- url     : https://prove2.me/theorems/f6a869be-aca9-5e15-a3be-36f680c78954
-- title:
--   crouzeix Polynomial Scalar Companion Closed Extension eq boundary Value of regularized: crouzeix Polynomial Scalar Companion Closed Extension eq boundary Value of regularized
-- statement:
--   Under the regularized convergence hypotheses, the canonical extension
--   takes the explicit regularized Plemelj value on the frontier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L600-L618
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L600-L618

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1)
    (hreg : ∀ xi ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
    {xi : ℂ} (hxi : xi ∈ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega p xi =
      crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi := by sorry
