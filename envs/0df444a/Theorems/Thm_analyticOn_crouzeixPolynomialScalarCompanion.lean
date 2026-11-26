-- Prove2me | Theorems.Thm_analyticOn_crouzeixPolynomialScalarCompanion
-- name    : analyticOn_crouzeixPolynomialScalarCompanion
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:35:25.595524+00:00
-- url     : https://prove2.me/theorems/eb382c0c-da3d-469e-bf45-cd216a95c30d
-- title:
--   analytic On crouzeix Polynomial Scalar Companion: analytic On crouzeix Polynomial Scalar Companion
-- statement:
--   The scalar Crouzeix--Palencia companion is holomorphic throughout the
--   smooth Jordan carrier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanion.lean#L479-L486
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanion.lean#L479-L486

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
set_option autoImplicit false
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real

theorem analyticOn_crouzeixPolynomialScalarCompanion
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    AnalyticOn ℂ (crouzeixPolynomialScalarCompanion Omega p)
      Omega.carrier := by sorry
