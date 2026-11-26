-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_smul_of_regularized
-- name    : crouzeixPolynomialScalarCompanionClosedExtension_smul_of_regularized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:04:11.539845+00:00
-- url     : https://prove2.me/theorems/e2f61a36-71c5-47e5-87d7-e4c028bee767
-- title:
--   crouzeix Polynomial Scalar Companion Closed Extension smul of regularized: crouzeix Polynomial Scalar Companion Closed Extension smul of regularized
-- statement:
--   Under winding normalization and regularized Plemelj convergence, the
--   canonical closed companion extension is conjugate-homogeneous on the whole
--   closure.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L668-L698
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L668-L698

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionClosedExtension_smul_of_regularized
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1)
    (hp : ∀ xi ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega (a • p) z =
      star a * crouzeixPolynomialScalarCompanionClosedExtension Omega p z := by sorry
