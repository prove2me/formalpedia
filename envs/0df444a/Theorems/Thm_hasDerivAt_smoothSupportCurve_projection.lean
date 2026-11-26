-- Prove2me | Theorems.Thm_hasDerivAt_smoothSupportCurve_projection
-- name    : hasDerivAt_smoothSupportCurve_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:07:46.222999+00:00
-- url     : https://prove2.me/theorems/b47bf9e5-59a2-486a-9b24-04f8004ba2c8
-- title:
--   has Deriv At smooth Support Curve projection: has Deriv At smooth Support Curve projection
-- statement:
--   Derivative witness for a fixed directional projection of the support
--   curve.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L73-L93
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L73-L93

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem hasDerivAt_smoothSupportCurve_projection
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    (theta phi : ℝ) :
    HasDerivAt
      (fun x => polytopeDirectionalValue (smoothSupportCurve h x) theta)
      (smoothSupportCurvatureRadius h phi * Real.sin (theta - phi)) phi := by sorry
