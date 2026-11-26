-- Prove2me | Theorems.Thm_contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
-- name    : contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:40:58.489425+00:00
-- url     : https://prove2.me/theorems/2a99a8c3-73bb-5d64-8981-e52f7c9142dd
-- title:
--   contour Integrable crouzeix Polynomial Scalar Companion Regularized self: contour Integrable crouzeix Polynomial Scalar Companion Regularized self
-- statement:
--   Cancellation makes the regularized kernel contour-integrable at its own
--   base point, even when that point lies on the frontier.  Polynomial division
--   factors the numerator by `sigma - xi`; after conjugation and multiplication
--   by its inverse, the remaining singular factor has norm one.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L276-L360
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L276-L360

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) :
    ContourIntegrable
      (fun sigma ↦
        (star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
          (sigma - xi)⁻¹)
      Omega.boundaryParam := by sorry
