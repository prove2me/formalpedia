-- Prove2me | Theorems.Thm_contourIntegral_eq_zero_of_diffContOnCl_smoothJordan
-- name    : contourIntegral_eq_zero_of_diffContOnCl_smoothJordan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:40:57.051956+00:00
-- url     : https://prove2.me/theorems/5d5db23a-e55c-5466-83f3-1d23bba82300
-- title:
--   contour Integral eq zero of diff Cont On Cl smooth Jordan: contour Integral eq zero of diff Cont On Cl smooth Jordan
-- statement:
--   A scalar function continuous on the closure of a smooth convex Jordan
--   domain and complex differentiable in its carrier has zero boundary contour
--   integral.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCauchy.lean#L24-L209
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCauchy.lean#L24-L209

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Sets.Compacts
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchy
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Topology

theorem contourIntegral_eq_zero_of_diffContOnCl_smoothJordan
    (Omega : SmoothJordanDomain) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f Omega.carrier) :
    contourIntegral f Omega.boundaryParam = 0 := by sorry
