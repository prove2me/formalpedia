-- Prove2me | Theorems.Thm_deriv_smoothSupportCurve_projection
-- name    : deriv_smoothSupportCurve_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:06:58.608827+00:00
-- url     : https://prove2.me/theorems/a20ae255-fb8e-5dc9-b743-140c9bf5c5a4
-- title:
--   deriv smooth Support Curve projection: deriv smooth Support Curve projection
-- statement:
--   The derivative of a fixed directional projection is the curvature radius
--   times the sine of the angular displacement.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L34-L69
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L34-L69

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem deriv_smoothSupportCurve_projection
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    (theta phi : ℝ) :
    deriv
      (fun x => polytopeDirectionalValue (smoothSupportCurve h x) theta) phi =
      smoothSupportCurvatureRadius h phi * Real.sin (theta - phi) := by sorry
