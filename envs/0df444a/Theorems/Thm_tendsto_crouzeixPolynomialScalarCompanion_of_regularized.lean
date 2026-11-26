-- Prove2me | Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanion_of_regularized
-- name    : tendsto_crouzeixPolynomialScalarCompanion_of_regularized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:39:54.66416+00:00
-- url     : https://prove2.me/theorems/75fb8aca-bc91-4084-9c8b-180081c45d98
-- title:
--   tendsto crouzeix Polynomial Scalar Companion of regularized: tendsto crouzeix Polynomial Scalar Companion of regularized
-- statement:
--   If the scalar winding kernel is normalized to one in the carrier, then
--   convergence of the cancelled transform at `xi` implies the actual Plemelj
--   limit there.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L553-L576
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L553-L576

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem tendsto_crouzeixPolynomialScalarCompanion_of_regularized
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1)
    (xi : ℂ)
    (hreg : Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi))) :
    Tendsto (crouzeixPolynomialScalarCompanion Omega p)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi)) := by sorry
