-- Prove2me | Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_regularized
-- name    : continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_regularized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:55:09.085131+00:00
-- url     : https://prove2.me/theorems/7fe84554-9e7e-4529-8af9-6eb5c93e8a71
-- title:
--   continuous On crouzeix Polynomial Scalar Companion Closed Extension of regularized: continuous On crouzeix Polynomial Scalar Companion Closed Extension of regularized
-- statement:
--   Frontierwise convergence of the regularized transforms makes the
--   canonical closed companion extension continuous.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L580-L596
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L580-L596

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_regularized
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1)
    (hreg : ∀ xi ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi))) :
    ContinuousOn
      (crouzeixPolynomialScalarCompanionClosedExtension Omega p)
      (closure Omega.carrier) := by sorry
