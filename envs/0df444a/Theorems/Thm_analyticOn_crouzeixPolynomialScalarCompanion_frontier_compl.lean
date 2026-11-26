-- Prove2me | Theorems.Thm_analyticOn_crouzeixPolynomialScalarCompanion_frontier_compl
-- name    : analyticOn_crouzeixPolynomialScalarCompanion_frontier_compl
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:03:31.015368+00:00
-- url     : https://prove2.me/theorems/7efc1c2a-b6b9-4d9e-b550-a29a7ad477bb
-- title:
--   analytic On crouzeix Polynomial Scalar Companion frontier compl: analytic On crouzeix Polynomial Scalar Companion frontier compl
-- statement:
--   The scalar companion is holomorphic on the complement of the smooth
--   Jordan frontier, giving both its interior and exterior branches.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanion.lean#L466-L475
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanion.lean#L466-L475

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
set_option autoImplicit false
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real

theorem analyticOn_crouzeixPolynomialScalarCompanion_frontier_compl
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    AnalyticOn ℂ (crouzeixPolynomialScalarCompanion Omega p)
      (frontier Omega.carrier)ᶜ := by sorry
