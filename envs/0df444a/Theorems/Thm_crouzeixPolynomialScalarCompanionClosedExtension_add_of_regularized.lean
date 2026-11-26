-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_add_of_regularized
-- name    : crouzeixPolynomialScalarCompanionClosedExtension_add_of_regularized
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:03:54.188801+00:00
-- url     : https://prove2.me/theorems/877ed2d0-8a3d-49a1-bc7a-675d2095d55f
-- title:
--   crouzeix Polynomial Scalar Companion Closed Extension add of regularized: crouzeix Polynomial Scalar Companion Closed Extension add of regularized
-- statement:
--   Under winding normalization and regularized Plemelj convergence for two
--   polynomials, the canonical closed companion extension preserves their sum on
--   the whole closure.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L623-L663
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L623-L663

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionClosedExtension_add_of_regularized
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1)
    (hp : ∀ xi ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
    (hq : ∀ xi ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega q xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega q xi xi)))
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega (p + q) z =
      crouzeixPolynomialScalarCompanionClosedExtension Omega p z +
        crouzeixPolynomialScalarCompanionClosedExtension Omega q z := by sorry
