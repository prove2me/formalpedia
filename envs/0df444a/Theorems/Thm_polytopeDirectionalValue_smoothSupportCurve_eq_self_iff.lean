-- Prove2me | Theorems.Thm_polytopeDirectionalValue_smoothSupportCurve_eq_self_iff
-- name    : polytopeDirectionalValue_smoothSupportCurve_eq_self_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:10:36.330264+00:00
-- url     : https://prove2.me/theorems/040ed9f1-0c45-4cd1-a21a-e6ba01950b14
-- title:
--   polytope Directional Value smooth Support Curve eq self iff: polytope Directional Value smooth Support Curve eq self iff
-- statement:
--   A directional projection reaches its support value exactly at parameters
--   congruent to the matching normal angle modulo `2 * pi`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L192-L238
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L192-L238

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem polytopeDirectionalValue_smoothSupportCurve_eq_self_iff
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    (hperiodic : Function.Periodic h (2 * Real.pi))
    (hcurv : ∀ x, 0 < smoothSupportCurvatureRadius h x)
    (theta phi : ℝ) :
    polytopeDirectionalValue (smoothSupportCurve h phi) theta = h theta ↔
      ∃ k : ℤ, phi = theta + (k : ℝ) * (2 * Real.pi) := by sorry
