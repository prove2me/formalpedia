-- Prove2me | Theorems.Thm_canonicalNormal_support_all_of_Ioc
-- name    : canonicalNormal_support_all_of_Ioc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:19:31.725934+00:00
-- url     : https://prove2.me/theorems/e89c7c12-174c-4107-a634-06c493c70d6a
-- title:
--   canonical Normal support all of Ioc: canonical Normal support all of Ioc
-- statement:
--   An oriented support inequality verified on the standard half-open
--   fundamental interval holds at every real parameter.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureMass.lean#L59-L80
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureMass.lean#L59-L80

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem canonicalNormal_support_all_of_Ioc
    (Omega : SmoothJordanDomain) (c : ℂ)
    (hsupport : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0) :
    ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0 := by sorry
